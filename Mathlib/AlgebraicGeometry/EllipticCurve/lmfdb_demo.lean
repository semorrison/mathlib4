import Mathlib.AlgebraicGeometry.EllipticCurve.lmfdb

#lmfdb «EllipticCurve/Q» «220890.c1»

def L := LMFDB.«EllipticCurve/Q».«220890.c1»

#eval L.b₈            -- -99286876
#check L.c_relation   -- 1728 * WeierstrassCurve.Δ L = WeierstrassCurve.c₄ L ^ 3 - WeierstrassCurve.c₆ L ^ 2
