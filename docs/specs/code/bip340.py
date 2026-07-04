"""
BIP-340 Schnorr signature verification over secp256k1.

Reference implementation in Sage for testing against the C++
Bip340Verify circuit.  Uses Sage's built-in elliptic curve
arithmetic with hashlib for SHA-256.
"""

import hashlib
from typing import Optional, Tuple

import sage.all  # type: ignore[import-untyped]


# secp256k1 parameters -------------------------------------------------------
P256K1_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
P256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P256K1_B = 7

# secp256k1 generator (affine).
_GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

# Lazy-initialized Sage objects (avoid module-level Sage for mypy).
_curve = None  # type: ignore[var-annotated]
_generator = None  # type: ignore[var-annotated]


def _get_curve():
    """Return the secp256k1 elliptic curve (Sage object)."""
    global _curve
    if _curve is None:
        Fp = sage.all.GF(P256K1_P)
        _curve = sage.all.EllipticCurve(Fp, [0, P256K1_B])
    return _curve


def _get_G():
    """Return the secp256k1 generator point (Sage object)."""
    global _generator
    if _generator is None:
        _generator = _get_curve()(_GX, _GY)
    return _generator


# BIP-340 tagged hash tag.
_CHALLENGE_TAG = b"BIP0340/challenge"
_TAG_HASH = hashlib.sha256(_CHALLENGE_TAG).digest()


def _tagged_hash(data: bytes) -> bytes:
    """BIP-340 tagged hash: SHA256(SHA256(tag) || SHA256(tag) || data)."""
    return hashlib.sha256(_TAG_HASH + _TAG_HASH + data).digest()


def _int_from_bytes(b: bytes) -> int:
    """Convert bytes to integer (big-endian)."""
    return int.from_bytes(b, "big")


def _bytes_from_int(x: int) -> bytes:
    """Convert integer to 32-byte big-endian."""
    return x.to_bytes(32, "big")


def _is_even(y: int) -> bool:
    """Check if an integer is even."""
    return (y & 1) == 0


def lift_x(x: int) -> Optional[Tuple[int, int]]:
    """
    BIP-340 lift_x: given an x-coordinate, compute the corresponding
    curve point with even y-coordinate.  Returns (x, y) or None if
    x is not on the curve.
    """
    if x >= P256K1_P:
        return None
    y_sq = (pow(x, 3, P256K1_P) + P256K1_B) % P256K1_P
    # p ≡ 3 mod 4, so sqrt is y_sq^((p+1)/4).
    y = pow(y_sq, (P256K1_P + 1) // 4, P256K1_P)
    if (y * y) % P256K1_P != y_sq:
        return None  # not a quadratic residue
    if not _is_even(y):
        y = P256K1_P - y
    return (x, y)


def verify(pk_bytes: bytes, msg: bytes, sig_bytes: bytes) -> bool:
    """
    BIP-340 Schnorr signature verification.

    Args:
        pk_bytes: 32-byte x-only public key.
        msg: message bytes.
        sig_bytes: 64-byte signature (r || s).

    Returns True if the signature is valid.
    """
    if len(pk_bytes) != 32 or len(sig_bytes) != 64:
        return False

    r_bytes = sig_bytes[:32]
    s_bytes = sig_bytes[32:]

    r = _int_from_bytes(r_bytes)
    s = _int_from_bytes(s_bytes)

    if r >= P256K1_P or s >= P256K1_N:
        return False

    # Lift public key.
    pk = lift_x(_int_from_bytes(pk_bytes))
    if pk is None:
        return False
    P = _get_curve()(pk[0], pk[1])

    # Challenge e = tagged_hash("BIP0340/challenge", r || P.x || msg) mod n.
    e_bytes = _tagged_hash(r_bytes + pk_bytes + msg)
    e = _int_from_bytes(e_bytes) % P256K1_N

    # Compute R' = s·G - e·P.
    sG = int(s) * _get_G()
    eP = int(e) * P
    Rp = sG - eP

    if Rp.is_zero():
        return False

    # Normalize and check x-coordinate + even y.
    Rx = int(Rp[0])
    Ry = int(Rp[1])
    if not _is_even(Ry):
        return False
    return Rx == r


# BIP-340 test vectors from Bitcoin Core.
# Source: https://raw.githubusercontent.com/bitcoin/bitcoin/refs/heads/master/test/functional/test_framework/bip340_test_vectors.csv
TEST_VECTORS = [
    # Index 0
    {
        "pk": bytes.fromhex("F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"),
        "msg": bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000000"),
        "sig": bytes.fromhex("E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0"),
        "valid": True,
    },
    # Index 1
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A"),
        "valid": True,
    },
    # Index 2
    {
        "pk": bytes.fromhex("DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8"),
        "msg": bytes.fromhex("7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C"),
        "sig": bytes.fromhex("5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7"),
        "valid": True,
    },
    # Index 3: test fails if msg is reduced modulo p or n
    {
        "pk": bytes.fromhex("25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517"),
        "msg": bytes.fromhex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"),
        "sig": bytes.fromhex("7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3"),
        "valid": True,
    },
    # Index 4
    {
        "pk": bytes.fromhex("D69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9"),
        "msg": bytes.fromhex("4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703"),
        "sig": bytes.fromhex("00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4"),
        "valid": True,
    },
    # Index 5: public key not on the curve
    {
        "pk": bytes.fromhex("EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B"),
        "valid": False,
    },
    # Index 6: has_even_y(R) is false
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2"),
        "valid": False,
    },
    # Index 7: negated message
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD"),
        "valid": False,
    },
    # Index 8: negated s value
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6"),
        "valid": False,
    },
    # Index 9: sG - eP is infinite (x(inf) as 0)
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("0000000000000000000000000000000000000000000000000000000000000000123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051"),
        "valid": False,
    },
    # Index 10: sG - eP is infinite (x(inf) as 1)
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("00000000000000000000000000000000000000000000000000000000000000017615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197"),
        "valid": False,
    },
    # Index 11: sig[0:32] is not an X coordinate on the curve
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B"),
        "valid": False,
    },
    # Index 12: sig[0:32] is equal to field size
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B"),
        "valid": False,
    },
    # Index 13: sig[32:64] is equal to curve order
    {
        "pk": bytes.fromhex("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        "valid": False,
    },
    # Index 14: public key exceeds field size
    {
        "pk": bytes.fromhex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30"),
        "msg": bytes.fromhex("243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89"),
        "sig": bytes.fromhex("6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B"),
        "valid": False,
    },
    # Index 15: message of size 0 (added 2022-12)
    {
        "pk": bytes.fromhex("778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117"),
        "msg": b"",
        "sig": bytes.fromhex("71535DB165ECD9FBBC046E5FFAEA61186BB6AD436732FCCC25291A55895464CF6069CE26BF03466228F19A3A62DB8A649F2D560FAC652827D1AF0574E427AB63"),
        "valid": True,
    },
    # Index 16: message of size 1 (added 2022-12)
    {
        "pk": bytes.fromhex("778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117"),
        "msg": bytes.fromhex("11"),
        "sig": bytes.fromhex("08A20A0AFEF64124649232E0693C583AB1B9934AE63B4C3511F3AE1134C6A303EA3173BFEA6683BD101FA5AA5DBC1996FE7CACFC5A577D33EC14564CEC2BACBF"),
        "valid": True,
    },
    # Index 17: message of size 17 (added 2022-12)
    {
        "pk": bytes.fromhex("778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117"),
        "msg": bytes.fromhex("0102030405060708090A0B0C0D0E0F1011"),
        "sig": bytes.fromhex("5130F39A4059B43BC7CAC09A19ECE52B5D8699D1A71E3C52DA9AFDB6B50AC370C4A482B77BF960F8681540E25B6771ECE1E5A37FD80E5A51897C5566A97EA5A5"),
        "valid": True,
    },
    # Index 18: message of size 100 (added 2022-12)
    {
        "pk": bytes.fromhex("778CAA53B4393AC467774D09497A87224BF9FAB6F6E68B23086497324D6FD117"),
        "msg": bytes.fromhex("99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"),
        "sig": bytes.fromhex("403B12B0D8555A344175EA7EC746566303321E5DBFA8BE6F091635163ECA79A8585ED3E3170807E7C03B720FC54C7B23897FCBA0E9D0B4A06894CFD249F22367"),
        "valid": True,
    },
]


def curve_order() -> int:
    """Return the secp256k1 curve order."""
    return P256K1_N


def field_modulus() -> int:
    """Return the secp256k1 base field modulus."""
    return P256K1_P


def generator() -> Tuple[int, int]:
    """Return the secp256k1 generator point (affine)."""
    return (_GX, _GY)
