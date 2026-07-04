"""
BIP-340 circuit and witness generation as a Longfellow sumcheck circuit.

Corresponds to lib/circuits/bip340/bip340_verify.h and
lib/circuits/bip340/bip340_witness.h.

Provides make_bip340_test_circuit() and make_bip340_witness() for
testing circuit evaluation with the sumcheck infrastructure.
"""

import hashlib
from typing import List, Optional, Tuple

import sage.all
from sage.rings.finite_rings.finite_field_constructor import GF

from circuit import Circuit, CircuitLayer, Quad
from fields import Fp256k1


# secp256k1 parameters.
P256K1_P = int(Fp256k1.order())
P256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P256K1_B = 7
_GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

F = Fp256k1
E = sage.all.EllipticCurve(Fp256k1, [0, P256K1_B])
G = E(_GX, _GY)


def lift_x(x: int) -> Optional[Tuple[int, int]]:
    """BIP-340 lift_x: compute even-y point for an x-coordinate."""
    if x >= P256K1_P:
        return None
    y_sq = (pow(x, 3, P256K1_P) + P256K1_B) % P256K1_P
    y = pow(y_sq, (P256K1_P + 1) // 4, P256K1_P)
    if (y * y) % P256K1_P != y_sq:
        return None
    if y & 1:
        y = P256K1_P - y
    return (x, y)


def tagged_hash(r_bytes: bytes, pk_bytes: bytes, msg: bytes) -> int:
    """BIP-340 tagged hash for challenge computation."""
    tag = b"BIP0340/challenge"
    tag_hash = hashlib.sha256(tag).digest()
    preimage = tag_hash + tag_hash + r_bytes + pk_bytes + msg
    return int.from_bytes(hashlib.sha256(preimage).digest(), "big")


def make_bip340_test_circuit() -> Circuit:
    """
    Construct a minimal BIP-340 verification circuit.

    The circuit checks three equations over Fp256k1:

      1. py² = px³ + b             (pk is on the curve)
      2. sG_x - eP_x - rx * sG_z = 0  (R.x == rx, projective)
      3. sG_y - eP_y - ry * sG_z = 0  (R.y == ry, projective; ry is provided)

    All intermediate values (sG, eP, py, px²) come from the witness.
    This is a simplified model of the C++ Bip340Verify circuit.
    """
    # Circuit topology (single layer):
    #   Inputs: [1, rx, px, e, sGx, sGy, sGz, ePx, ePy, ePz, py, ry, px², px³]
    #                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    #                                      public           witness
    #
    #   pub = 4  (constant 1 + rx, px, e)
    #   inputs = 14

    K = F

    layer_0 = CircuitLayer(
        num_input_wires=14,
        quads=[
            # Gate 0: 0 = py² - px³ - b  (point on curve check)
            Quad(gate=0, input_0=10, input_1=10, coefficient=K(1)),       # +py²
            Quad(gate=0, input_0=13, input_1=0,  coefficient=K(-1)),      # -px³
            Quad(gate=0, input_0=0,  input_1=0,  coefficient=K(-P256K1_B)),  # -b

            # Gate 1: 0 = sGx - ePx - rx * sGz  (R.x projective equality)
            Quad(gate=1, input_0=4,  input_1=0,  coefficient=K(1)),       # +sGx
            Quad(gate=1, input_0=7,  input_1=0,  coefficient=K(-1)),      # -ePx
            Quad(gate=1, input_0=1,  input_1=6,  coefficient=K(-1)),      # -rx*sGz

            # Gate 2: 0 = sGy - ePy - ry * sGz  (R.y projective equality)
            Quad(gate=2, input_0=5,  input_1=0,  coefficient=K(1)),       # +sGy
            Quad(gate=2, input_0=8,  input_1=0,  coefficient=K(-1)),      # -ePy
            Quad(gate=2, input_0=11, input_1=6,  coefficient=K(-1)),      # -ry*sGz
        ],
        field=K,
    )
    return Circuit(
        num_outputs=3,         # 3 assertion gates
        num_public_inputs=4,   # 1 + rx + px + e
        num_inputs=14,
        layers=[layer_0],
    )


def make_bip340_witness(
    sig_bytes: bytes,
    pk_bytes: bytes,
    msg: bytes,
) -> List[int]:
    """
    Generate witness for make_bip340_test_circuit().

    Returns 14 field elements (as Fp256k1 elements).
    Index layout matches the circuit input order:
      [0]=1  [1]=rx  [2]=px  [3]=e
      [4]=sGx  [5]=sGy  [6]=sGz
      [7]=ePx  [8]=ePy  [9]=ePz
      [10]=py  [11]=ry  [12]=px²  [13]=px³
    """
    # Parse signature.
    r = int.from_bytes(sig_bytes[:32], "big")
    s = int.from_bytes(sig_bytes[32:], "big")
    px = int.from_bytes(pk_bytes, "big")

    # Challenge e.
    e = tagged_hash(sig_bytes[:32], pk_bytes, msg) % P256K1_N

    # Lift public key.
    pk_pt = lift_x(px)
    assert pk_pt is not None
    py = pk_pt[1]

    # Compute s·G.
    sG = int(s) * G

    # Compute e·P.
    P = E(pk_pt[0], pk_pt[1])
    eP = int(e) * P

    # R = sG - eP (on the curve).
    R = sG - eP
    assert not R.is_zero()

    Rx = int(R[0])
    Ry = int(R[1])
    Rz = int(R[2])

    # Build witness (as Fp256k1 elements).
    K = Fp256k1
    return [
        K(1),            # 0: constant 1
        K(r),            # 1: rx (public)
        K(px),           # 2: px (public)
        K(e % P256K1_P), # 3: e (public)
        K(int(sG[0])),   # 4: sGx
        K(int(sG[1])),   # 5: sGy
        K(int(sG[2])),   # 6: sGz
        K(int(eP[0])),   # 7: ePx
        K(int(eP[1])),   # 8: ePy
        K(int(eP[2])),   # 9: ePz
        K(py),           # 10: py
        K(Ry),           # 11: ry (R.y, for projective y-check)
        K((px * px) % P256K1_P),     # 12: px²
        K((px * px * px) % P256K1_P),  # 13: px³
    ]


def verify_signature(sig_bytes: bytes, pk_bytes: bytes, msg: bytes) -> bool:
    """
    Verify a BIP-340 signature using Sage EC arithmetic.
    Same logic as the standalone bip340.py, duplicated for self-contained use.
    """
    if len(pk_bytes) != 32 or len(sig_bytes) != 64:
        return False

    r_bytes = sig_bytes[:32]
    s_bytes = sig_bytes[32:]
    r = int.from_bytes(r_bytes, "big")
    s = int.from_bytes(s_bytes, "big")

    if r >= P256K1_P or s >= P256K1_N:
        return False

    pk = lift_x(int.from_bytes(pk_bytes, "big"))
    if pk is None:
        return False
    P = E(pk[0], pk[1])

    e = tagged_hash(r_bytes, pk_bytes, msg) % P256K1_N

    R = int(s) * G - int(e) * P
    if R.is_zero():
        return False

    Rx = int(R[0])
    Ry = int(R[1])
    if Ry & 1:
        return False
    return Rx == r
