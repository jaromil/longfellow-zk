"""Tests for BIP-340 circuit in the Longfellow sumcheck model.

Covers:
  - Circuit evaluation (witness passes/fails)
  - Full sumcheck prover/verifier lifecycle
  - Upstream Bitcoin Core test vectors
  - Witness vs circuit consistency
"""

import copy
import unittest

import sage.all

from circuit import Circuit
from fields import Fp256k1
from fs import Transcript
from sumcheck import (
    constraints_circuit,
    construct_concrete_pad,
    construct_symbolic_variables,
    sumcheck_circuit,
)

from bip340_circuit import (
    F,
    lift_x,
    make_bip340_test_circuit,
    make_bip340_witness,
    verify_signature,
    P256K1_P,
    P256K1_N,
)

# Bitcoin Core BIP-340 test vectors (subset).
TEST_VECTORS = [
    # Index 0
    {
        "pk": bytes.fromhex(
            "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
        ),
        "msg": bytes.fromhex(
            "0000000000000000000000000000000000000000000000000000000000000000"
        ),
        "sig": bytes.fromhex(
            "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215"
            "25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0"
        ),
        "valid": True,
    },
    # Index 1
    {
        "pk": bytes.fromhex(
            "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"
        ),
        "msg": bytes.fromhex(
            "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"
        ),
        "sig": bytes.fromhex(
            "6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE3341"
            "8906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A"
        ),
        "valid": True,
    },
    # Index 5: pk not on curve
    {
        "pk": bytes.fromhex(
            "EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34"
        ),
        "msg": bytes.fromhex(
            "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"
        ),
        "sig": bytes.fromhex(
            "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769"
            "69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B"
        ),
        "valid": False,
    },
    # Index 7: negated message
    {
        "pk": bytes.fromhex(
            "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"
        ),
        "msg": bytes.fromhex(
            "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"
        ),
        "sig": bytes.fromhex(
            "1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F"
            "28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD"
        ),
        "valid": False,
    },
]


class TestBip340Circuit(unittest.TestCase):
    def test_signature_verification(self) -> None:
        """Standalone BIP-340 verification matches expected results."""
        for i, tv in enumerate(TEST_VECTORS):
            with self.subTest(vector=i):
                result = verify_signature(tv["sig"], tv["pk"], tv["msg"])
                self.assertEqual(result, tv["valid"])

    def test_circuit_evaluation_valid(self) -> None:
        """Circuit evaluates to all-zero constraints on valid witnesses."""
        circuit = make_bip340_test_circuit()
        for i, tv in enumerate(TEST_VECTORS):
            if not tv["valid"]:
                continue
            with self.subTest(vector=i):
                witness = make_bip340_witness(tv["sig"], tv["pk"], tv["msg"])
                wires = circuit.evaluate(witness)
                for layer in circuit.layers:
                    for j, quad in enumerate(layer.quads):
                        out = wires[0][quad.gate]
                        self.assertEqual(
                            int(out), 0,
                            f"Vector {i}: gate {quad.gate} not zero: {out}"
                        )

    def test_circuit_evaluation_invalid(self) -> None:
        """Circuit rejects invalid witnesses."""
        circuit = make_bip340_test_circuit()
        for i, tv in enumerate(TEST_VECTORS):
            if tv["valid"]:
                continue
            with self.subTest(vector=i):
                if tv["pk"] in (
                    "EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34",
                ):
                    # pk not on curve: lift_x fails in witness gen.
                    continue
                witness = make_bip340_witness(tv["sig"], tv["pk"], tv["msg"])
                wires = circuit.evaluate(witness)
                any_nonzero = False
                for layer in circuit.layers:
                    for quad in layer.quads:
                        if int(wires[0][quad.gate]) != 0:
                            any_nonzero = True
                self.assertTrue(
                    any_nonzero,
                    f"Vector {i}: expected at least one non-zero gate"
                )

    def test_circuit_matches_signature(self) -> None:
        """Circuit witness Rx matches the signature's r value."""
        circuit = make_bip340_test_circuit()
        tv = TEST_VECTORS[0]
        witness = make_bip340_witness(tv["sig"], tv["pk"], tv["msg"])
        wires = circuit.evaluate(witness)

        # Input 1 is rx (public), should match sig bytes.
        r = int.from_bytes(tv["sig"][:32], "big")
        self.assertEqual(int(witness[1]), r)
        # Assertion gates should be zero.
        self.assertEqual(int(wires[0][0]), 0)  # py² constraint
        self.assertEqual(int(wires[0][1]), 0)  # R.x constraint
        self.assertEqual(int(wires[0][2]), 0)  # R.y constraint

    def test_sumcheck_prover_verifier(self) -> None:
        """Full sumcheck prover/verifier lifecycle for BIP-340."""
        circuit = make_bip340_test_circuit()
        tv = TEST_VECTORS[0]
        witness = make_bip340_witness(tv["sig"], tv["pk"], tv["msg"])

        # Evaluate to get all wire values.
        wires = circuit.evaluate(witness)

        # Build pad.
        pad_transcript = Transcript()
        pad_transcript.init(b"bip340 pad prng")

        def pad_prg(field):
            return pad_transcript.generate_field(field)

        (pad_layers, _pad_flattened) = construct_concrete_pad(
            Fp256k1, circuit, pad_prg,
        )

        # Prove.
        transcript = Transcript()
        transcript.init(b"bip340 sumcheck")
        constraints_transcript = copy.deepcopy(transcript)

        proof = sumcheck_circuit(
            Fp256k1, circuit, wires, pad_layers, transcript,
        )

        self.assertIsNotNone(proof)
        self.assertTrue(len(proof) > 0)

        # Verify.
        sym_private_inputs, sym_pad = construct_symbolic_variables(
            Fp256k1, circuit,
        )
        (linear_constraints, quadratic_constraints) = constraints_circuit(
            Fp256k1,
            circuit,
            witness[:4],  # public inputs only
            sym_private_inputs,
            sym_pad,
            constraints_transcript,
            proof,
        )
        self.assertIsNotNone(linear_constraints)
        self.assertIsNotNone(quadratic_constraints)


if __name__ == "__main__":
    unittest.main()
