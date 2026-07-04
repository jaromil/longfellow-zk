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


# Known BIP-340 test vectors (from the BIP specification).
TEST_VECTORS = [
    # Index 0: sk=0x00...03, empty message.
    {
        "pk": bytes.fromhex(
            "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
        ),
        "msg": b"",
        "sig": bytes.fromhex(
            "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215"
            "25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0"
        ),
        "valid": True,
    },
    # Index 1: sk=0xB7E1..., message from BIP vector 1.
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
    # Altered signature (wrong R.x).
    {
        "pk": bytes.fromhex(
            "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
        ),
        "msg": b"",
        "sig": bytes.fromhex(
            "0000000000000000000000000000000000000000000000000000000000000000"
            "25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0"
        ),
        "valid": False,  # wrong R.x
    },
    # Wrong message.
    {
        "pk": bytes.fromhex(
            "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
        ),
        "msg": b"wrong",
        "sig": bytes.fromhex(
            "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215"
            "25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0"
        ),
        "valid": False,  # sig made for empty msg
    },
    # s >= n (invalid).
    {
        "pk": bytes.fromhex(
            "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
        ),
        "msg": b"",
        "sig": bytes.fromhex(
            "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215"
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
        ),
        "valid": False,  # s == n (not < n)
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
