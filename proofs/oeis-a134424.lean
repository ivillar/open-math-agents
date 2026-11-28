import OMAStatements.S_oeis_a134424

-- Problem: A134424: Area under all paths in the first quadrant from (0,0) to (n,0) using steps U=(1,1), D=(1,-1), h=(1,0) and H=(2,0).
-- Upstream: formal-conjectures statements/oeis-a134424.lean:0 (declaration OMA.S_oeis_a134424.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A134424Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 2 + 2 * X ^ 4 + X ^ 6 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 - 24 * X ^ 7 - 6 * X ^ 8 + 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-5 * X ^ 2 - 5 * X ^ 3 + 135 * X ^ 4 + 10 * X ^ 5 - 725 * X ^ 6 - 235 * X ^ 7 + 725 * X ^ 8 + 10 * X ^ 9 - 135 * X ^ 10 - 5 * X ^ 11 + 5 * X ^ 12) * derivative ℚ (derivative ℚ G) + (-8 * X + 107 * X ^ 2 + 20 * X ^ 3 - 480 * X ^ 4 - 1584 * X ^ 5 - 705 * X ^ 6 + 2766 * X ^ 7 + 540 * X ^ 8 - 790 * X ^ 9 - 137 * X ^ 10 + 22 * X ^ 11) * derivative ℚ G + (14 + 244 * X - 812 * X ^ 2 - 1776 * X ^ 3 + 2430 * X ^ 4 + 2352 * X ^ 5 - 1248 * X ^ 6 - 756 * X ^ 7 + 42 * X ^ 8) * G =
      -12 * X ^ 2 + 288 * X ^ 3 + 288 * X ^ 5 + 12 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d19 : derivative ℚ (19 : ℚ⟦X⟧) = 0 := dnum 19
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d38 : derivative ℚ (38 : ℚ⟦X⟧) = 0 := dnum 38
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d112 : derivative ℚ (112 : ℚ⟦X⟧) = 0 := dnum 112
  have d114 : derivative ℚ (114 : ℚ⟦X⟧) = 0 := dnum 114
  have d120 : derivative ℚ (120 : ℚ⟦X⟧) = 0 := dnum 120
  have d168 : derivative ℚ (168 : ℚ⟦X⟧) = 0 := dnum 168
  have hp0 : (1 * (X * X) + 2 * (X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X + 3 * (X * X) - 16 * (X * X * X) - 5 * (X * X * X * X) - 5 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) + 3 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) - 6 * (X * X * X * X) + 24 * (X * X * X * X * X) + 19 * (X * X * X * X * X * X) - 24 * (X * X * X * X * X * X * X) - 6 * (X * X * X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X) + 2 * (X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X + 3 * (X * X) - 16 * (X * X * X) - 5 * (X * X * X * X) - 5 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) + 3 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) - 6 * (X * X * X * X) + 24 * (X * X * X * X * X) + 19 * (X * X * X * X * X * X) - 24 * (X * X * X * X * X * X * X) - 6 * (X * X * X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (2 * X + 8 * X ^ 3 + 6 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) + (4 + 6 * X - 48 * X ^ 2 - 20 * X ^ 3 - 30 * X ^ 5 + 112 * X ^ 6 + 24 * X ^ 7 - 36 * X ^ 8 - 10 * X ^ 9 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 - 24 * X ^ 3 + 120 * X ^ 4 + 114 * X ^ 5 - 168 * X ^ 6 - 48 * X ^ 7 + 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d5, d6, d16, d19, d24]
    ring
  have hd1 : (2 * X + 8 * X ^ 3 + 6 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) + (4 + 6 * X - 48 * X ^ 2 - 20 * X ^ 3 - 30 * X ^ 5 + 112 * X ^ 6 + 24 * X ^ 7 - 36 * X ^ 8 - 10 * X ^ 9 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 - 24 * X ^ 3 + 120 * X ^ 4 + 114 * X ^ 5 - 168 * X ^ 6 - 48 * X ^ 7 + 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (2 * X + 8 * (X * X * X) + 6 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X + 3 * (X * X) - 16 * (X * X * X) - 5 * (X * X * X * X) - 5 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) + 3 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 + 6 * X - 48 * (X * X) - 20 * (X * X * X) - 30 * (X * X * X * X * X) + 112 * (X * X * X * X * X * X) + 24 * (X * X * X * X * X * X * X) - 36 * (X * X * X * X * X * X * X * X) - 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 8 * (X * X * X) - 12 * (X * X * X * X) + 48 * (X * X * X * X * X) + 38 * (X * X * X * X * X * X) - 48 * (X * X * X * X * X * X * X) - 12 * (X * X * X * X * X * X * X * X) + 8 * (X * X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * (X * X) - 24 * (X * X * X) + 120 * (X * X * X * X) + 114 * (X * X * X * X * X) - 168 * (X * X * X * X * X * X) - 48 * (X * X * X * X * X * X * X) + 36 * (X * X * X * X * X * X * X * X) + 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((2 * X + 8 * (X * X * X) + 6 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X + 3 * (X * X) - 16 * (X * X * X) - 5 * (X * X * X * X) - 5 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) + 3 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 + 6 * X - 48 * (X * X) - 20 * (X * X * X) - 30 * (X * X * X * X * X) + 112 * (X * X * X * X * X * X) + 24 * (X * X * X * X * X * X * X) - 36 * (X * X * X * X * X * X * X * X) - 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 8 * (X * X * X) - 12 * (X * X * X * X) + 48 * (X * X * X * X * X) + 38 * (X * X * X * X * X * X) - 48 * (X * X * X * X * X * X * X) - 12 * (X * X * X * X * X * X * X * X) + 8 * (X * X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * (X * X) - 24 * (X * X * X) + 120 * (X * X * X * X) + 114 * (X * X * X * X * X) - 168 * (X * X * X * X * X * X) - 48 * (X * X * X * X * X * X * X) + 36 * (X * X * X * X * X * X * X * X) + 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (2 + 24 * X ^ 2 + 30 * X ^ 4 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 + 12 * X - 96 * X ^ 2 - 40 * X ^ 3 - 60 * X ^ 5 + 224 * X ^ 6 + 48 * X ^ 7 - 72 * X ^ 8 - 20 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 96 * X - 60 * X ^ 2 - 150 * X ^ 4 + 672 * X ^ 5 + 168 * X ^ 6 - 288 * X ^ 7 - 90 * X ^ 8 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 - 96 * X ^ 3 + 480 * X ^ 4 + 456 * X ^ 5 - 672 * X ^ 6 - 192 * X ^ 7 + 144 * X ^ 8 + 40 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 24 * X - 72 * X ^ 2 + 480 * X ^ 3 + 570 * X ^ 4 - 1008 * X ^ 5 - 336 * X ^ 6 + 288 * X ^ 7 + 90 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d5, d6, d8, d10, d12, d16, d20, d24, d30, d36, d38, d48, d112, d114, d120, d168]
    ring
  have hd2 : (2 + 24 * X ^ 2 + 30 * X ^ 4 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 + 12 * X - 96 * X ^ 2 - 40 * X ^ 3 - 60 * X ^ 5 + 224 * X ^ 6 + 48 * X ^ 7 - 72 * X ^ 8 - 20 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 96 * X - 60 * X ^ 2 - 150 * X ^ 4 + 672 * X ^ 5 + 168 * X ^ 6 - 288 * X ^ 7 - 90 * X ^ 8 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 - 96 * X ^ 3 + 480 * X ^ 4 + 456 * X ^ 5 - 672 * X ^ 6 - 192 * X ^ 7 + 144 * X ^ 8 + 40 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 24 * X - 72 * X ^ 2 + 480 * X ^ 3 + 570 * X ^ 4 - 1008 * X ^ 5 - 336 * X ^ 6 + 288 * X ^ 7 + 90 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G) ^ 3 * ((-5 * X ^ 2 - 5 * X ^ 3 + 135 * X ^ 4 + 10 * X ^ 5 - 725 * X ^ 6 - 235 * X ^ 7 + 725 * X ^ 8 + 10 * X ^ 9 - 135 * X ^ 10 - 5 * X ^ 11 + 5 * X ^ 12) * derivative ℚ (derivative ℚ G) + (-8 * X + 107 * X ^ 2 + 20 * X ^ 3 - 480 * X ^ 4 - 1584 * X ^ 5 - 705 * X ^ 6 + 2766 * X ^ 7 + 540 * X ^ 8 - 790 * X ^ 9 - 137 * X ^ 10 + 22 * X ^ 11) * derivative ℚ G + (14 + 244 * X - 812 * X ^ 2 - 1776 * X ^ 3 + 2430 * X ^ 4 + 2352 * X ^ 5 - 1248 * X ^ 6 - 756 * X ^ 7 + 42 * X ^ 8) * G - (-12 * X ^ 2 + 288 * X ^ 3 + 288 * X ^ 5 + 12 * X ^ 6)) = 0 := by
    linear_combination ((14 + 100 * X - 2306 * X ^ 2 + 7556 * X ^ 3 + 14860 * X ^ 4 - 87292 * X ^ 5 - 27524 * X ^ 6 + 372392 * X ^ 7 + 89866 * X ^ 8 - 687152 * X ^ 9 - 555894 * X ^ 10 + 80864 * X ^ 11 + 823606 * X ^ 12 + 1578040 * X ^ 13 + 235654 * X ^ 14 - 2988272 * X ^ 15 + 2362402 * X ^ 16 + 6733192 * X ^ 17 - 7998078 * X ^ 18 - 8666880 * X ^ 19 + 8556430 * X ^ 20 + 5391392 * X ^ 21 - 4069634 * X ^ 22 - 1933880 * X ^ 23 + 955796 * X ^ 24 + 428564 * X ^ 25 - 103420 * X ^ 26 - 54828 * X ^ 27 + 2154 * X ^ 28 + 3108 * X ^ 29 + 330 * X ^ 30 : ℚ⟦X⟧) + (-96 * X ^ 2 - 280 * X ^ 3 + 10832 * X ^ 4 - 33480 * X ^ 5 - 98416 * X ^ 6 + 447096 * X ^ 7 + 407616 * X ^ 8 - 2355624 * X ^ 9 - 1453072 * X ^ 10 + 6273088 * X ^ 11 + 4771488 * X ^ 12 - 8742368 * X ^ 13 - 8587952 * X ^ 14 + 7680312 * X ^ 15 + 7395360 * X ^ 16 - 627720 * X ^ 17 + 3104976 * X ^ 18 - 9517216 * X ^ 19 - 10351904 * X ^ 20 + 11358336 * X ^ 21 + 6516272 * X ^ 22 - 4562280 * X ^ 23 - 2273664 * X ^ 24 + 718776 * X ^ 25 + 443440 * X ^ 26 - 9032 * X ^ 27 - 34896 * X ^ 28 - 6232 * X ^ 29 - 320 * X ^ 30 : ℚ⟦X⟧) * G + (96 * X ^ 4 + 280 * X ^ 5 - 11120 * X ^ 6 + 32256 * X ^ 7 + 128736 * X ^ 8 - 510360 * X ^ 9 - 735520 * X ^ 10 + 3231360 * X ^ 11 + 3179888 * X ^ 12 - 10707632 * X ^ 13 - 10821584 * X ^ 14 + 20298240 * X ^ 15 + 23453440 * X ^ 16 - 27887160 * X ^ 17 - 34536480 * X ^ 18 + 27838272 * X ^ 19 + 29579280 * X ^ 20 - 18026800 * X ^ 21 - 12944688 * X ^ 22 + 5463232 * X ^ 23 + 3425920 * X ^ 24 - 664600 * X ^ 25 - 526720 * X ^ 26 - 8384 * X ^ 27 + 33936 * X ^ 28 + 6232 * X ^ 29 + 320 * X ^ 30 : ℚ⟦X⟧) * G ^ 2) * hP +
      ((-8 * X + 131 * X ^ 2 - 856 * X ^ 3 + 2002 * X ^ 4 + 5340 * X ^ 5 - 36488 * X ^ 6 + 21206 * X ^ 7 + 193186 * X ^ 8 - 237694 * X ^ 9 - 427037 * X ^ 10 + 488808 * X ^ 11 + 14112 * X ^ 12 + 603734 * X ^ 13 + 2055579 * X ^ 14 - 2783812 * X ^ 15 - 3377110 * X ^ 16 + 2262658 * X ^ 17 + 563471 * X ^ 18 + 1004084 * X ^ 19 + 2371448 * X ^ 20 - 2418662 * X ^ 21 - 1993513 * X ^ 22 + 1218356 * X ^ 23 + 774714 * X ^ 24 - 251794 * X ^ 25 - 165572 * X ^ 26 + 16760 * X ^ 27 + 17598 * X ^ 28 + 894 * X ^ 29 - 621 * X ^ 30 - 78 * X ^ 31 : ℚ⟦X⟧) + (-10 * X ^ 4 + 70 * X ^ 5 + 280 * X ^ 6 - 2970 * X ^ 7 + 700 * X ^ 8 + 35850 * X ^ 9 - 36320 * X ^ 10 - 213990 * X ^ 11 + 242850 * X ^ 12 + 727700 * X ^ 13 - 660960 * X ^ 14 - 1330140 * X ^ 15 + 666310 * X ^ 16 + 771330 * X ^ 17 + 771330 * X ^ 19 - 666310 * X ^ 20 - 1330140 * X ^ 21 + 660960 * X ^ 22 + 727700 * X ^ 23 - 242850 * X ^ 24 - 213990 * X ^ 25 + 36320 * X ^ 26 + 35850 * X ^ 27 - 700 * X ^ 28 - 2970 * X ^ 29 - 280 * X ^ 30 + 70 * X ^ 31 + 10 * X ^ 32 : ℚ⟦X⟧) * (derivative ℚ G) + (-8 * X ^ 3 - 284 * X ^ 4 + 4628 * X ^ 5 - 16904 * X ^ 6 - 34948 * X ^ 7 + 289180 * X ^ 8 - 62564 * X ^ 9 - 1896592 * X ^ 10 + 1391820 * X ^ 11 + 6481216 * X ^ 12 - 4940248 * X ^ 13 - 11134936 * X ^ 14 + 5829472 * X ^ 15 + 3829596 * X ^ 16 + 473580 * X ^ 17 + 13139664 * X ^ 18 - 8829348 * X ^ 19 - 18128144 * X ^ 20 + 9600872 * X ^ 21 + 9528184 * X ^ 22 - 3950880 * X ^ 23 - 2811188 * X ^ 24 + 736476 * X ^ 25 + 499520 * X ^ 26 - 50348 * X ^ 27 - 48436 * X ^ 28 - 1532 * X ^ 29 + 1824 * X ^ 30 + 212 * X ^ 31 : ℚ⟦X⟧) * G + (20 * X ^ 6 - 140 * X ^ 7 - 620 * X ^ 8 + 6280 * X ^ 9 + 620 * X ^ 10 - 86380 * X ^ 11 + 61860 * X ^ 12 + 609240 * X ^ 13 - 518160 * X ^ 14 - 2548440 * X ^ 15 + 1752480 * X ^ 16 + 6339240 * X ^ 17 - 2792500 * X ^ 18 - 8566700 * X ^ 19 + 2792500 * X ^ 20 + 6339240 * X ^ 21 - 1752480 * X ^ 22 - 2548440 * X ^ 23 + 518160 * X ^ 24 + 609240 * X ^ 25 - 61860 * X ^ 26 - 86380 * X ^ 27 - 620 * X ^ 28 + 6280 * X ^ 29 + 620 * X ^ 30 - 140 * X ^ 31 - 20 * X ^ 32 : ℚ⟦X⟧) * G * (derivative ℚ G) + (28 * X ^ 5 + 144 * X ^ 6 - 5332 * X ^ 7 + 22600 * X ^ 8 + 50308 * X ^ 9 - 424120 * X ^ 10 - 20460 * X ^ 11 + 3326344 * X ^ 12 - 1521560 * X ^ 13 - 14503616 * X ^ 14 + 7419848 * X ^ 15 + 36870024 * X ^ 16 - 14977420 * X ^ 17 - 51400200 * X ^ 18 + 18532580 * X ^ 19 + 39200856 * X ^ 20 - 13609912 * X ^ 21 - 16077664 * X ^ 22 + 4696360 * X ^ 23 + 3984536 * X ^ 24 - 762780 * X ^ 25 - 612440 * X ^ 26 + 42868 * X ^ 27 + 52760 * X ^ 28 + 2108 * X ^ 29 - 1824 * X ^ 30 - 212 * X ^ 31 : ℚ⟦X⟧) * G ^ 2) * hd1 +
      ((-5 * X ^ 2 + 35 * X ^ 3 + 125 * X ^ 4 - 1400 * X ^ 5 + 810 * X ^ 6 + 14450 * X ^ 7 - 19300 * X ^ 8 - 69810 * X ^ 9 + 102375 * X ^ 10 + 178205 * X ^ 11 - 201305 * X ^ 12 - 182740 * X ^ 13 + 18465 * X ^ 14 - 194715 * X ^ 15 + 342125 * X ^ 16 + 503850 * X ^ 17 - 342125 * X ^ 18 - 194715 * X ^ 19 - 18465 * X ^ 20 - 182740 * X ^ 21 + 201305 * X ^ 22 + 178205 * X ^ 23 - 102375 * X ^ 24 - 69810 * X ^ 25 + 19300 * X ^ 26 + 14450 * X ^ 27 - 810 * X ^ 28 - 1400 * X ^ 29 - 125 * X ^ 30 + 35 * X ^ 31 + 5 * X ^ 32 : ℚ⟦X⟧) + (20 * X ^ 4 - 140 * X ^ 5 - 560 * X ^ 6 + 5940 * X ^ 7 - 1400 * X ^ 8 - 71700 * X ^ 9 + 72640 * X ^ 10 + 427980 * X ^ 11 - 485700 * X ^ 12 - 1455400 * X ^ 13 + 1321920 * X ^ 14 + 2660280 * X ^ 15 - 1332620 * X ^ 16 - 1542660 * X ^ 17 - 1542660 * X ^ 19 + 1332620 * X ^ 20 + 2660280 * X ^ 21 - 1321920 * X ^ 22 - 1455400 * X ^ 23 + 485700 * X ^ 24 + 427980 * X ^ 25 - 72640 * X ^ 26 - 71700 * X ^ 27 + 1400 * X ^ 28 + 5940 * X ^ 29 + 560 * X ^ 30 - 140 * X ^ 31 - 20 * X ^ 32 : ℚ⟦X⟧) * G + (-20 * X ^ 6 + 140 * X ^ 7 + 620 * X ^ 8 - 6280 * X ^ 9 - 620 * X ^ 10 + 86380 * X ^ 11 - 61860 * X ^ 12 - 609240 * X ^ 13 + 518160 * X ^ 14 + 2548440 * X ^ 15 - 1752480 * X ^ 16 - 6339240 * X ^ 17 + 2792500 * X ^ 18 + 8566700 * X ^ 19 - 2792500 * X ^ 20 - 6339240 * X ^ 21 + 1752480 * X ^ 22 + 2548440 * X ^ 23 - 518160 * X ^ 24 - 609240 * X ^ 25 + 61860 * X ^ 26 + 86380 * X ^ 27 + 620 * X ^ 28 - 6280 * X ^ 29 - 620 * X ^ 30 + 140 * X ^ 31 + 20 * X ^ 32 : ℚ⟦X⟧) * G ^ 2) * hd2
  have hPG : (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 - 12 * X ^ 4 + 48 * X ^ 5 + 38 * X ^ 6 - 48 * X ^ 7 - 12 * X ^ 8 + 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 2 + 2 * X ^ 4 + X ^ 6 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 - 24 * X ^ 7 - 6 * X ^ 8 + 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-5) + derivative ℚ (derivative ℚ G) * X * X * X * C (-5) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 135 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 10 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-725) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-235) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 725 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * C 10 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * C (-135) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * X * C (-5) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * X * X * C 5 + derivative ℚ G * X * C (-8) +
      derivative ℚ G * X * X * C 107 + derivative ℚ G * X * X * X * C 20 +
      derivative ℚ G * X * X * X * X * C (-480) + derivative ℚ G * X * X * X * X * X * C (-1584) +
      derivative ℚ G * X * X * X * X * X * X * C (-705) + derivative ℚ G * X * X * X * X * X * X * X * C 2766 +
      derivative ℚ G * X * X * X * X * X * X * X * X * C 540 + derivative ℚ G * X * X * X * X * X * X * X * X * X * C (-790) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * X * C (-137) + derivative ℚ G * X * X * X * X * X * X * X * X * X * X * X * C 22 +
      G * C 14 + G * X * C 244 +
      G * X * X * C (-812) + G * X * X * X * C (-1776) +
      G * X * X * X * X * C 2430 + G * X * X * X * X * X * C 2352 +
      G * X * X * X * X * X * X * C (-1248) + G * X * X * X * X * X * X * X * C (-756) +
      G * X * X * X * X * X * X * X * X * C 42 =
      C (-12) * X * X + C 288 * X * X * X +
      C 288 * X * X * X * X * X + C 12 * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 2 + 2 * X ^ 4 + X ^ 6 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 - 24 * X ^ 7 - 6 * X ^ 8 + 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-5) * ((m : ℚ) + 12) * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 11) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      135 * ((m : ℚ) + 10) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 10 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-725) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-235) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      725 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 10 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-135) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      5 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-8) * ((m : ℚ) + 12) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      107 * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 20 * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-480) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1584) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-705) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2766 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      540 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-790) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-137) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 22 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      14 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 244 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-812) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1776) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2430 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2352 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1248) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-756) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      42 * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 2 + 2 * X ^ 4 + X ^ 6 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 - 24 * X ^ 7 - 6 * X ^ 8 + 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-450) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      7560 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 420 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-21750) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4700) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      8700 * coeff (0 + 1 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1) G +
      (-270) * coeff (0 + 1 + 1) G + (-80) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      963 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 160 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3360) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9504) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3525) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 11064 * coeff (0 + 1 + 1 + 1 + 1) G +
      1620 * coeff (0 + 1 + 1 + 1) G + (-1580) * coeff (0 + 1 + 1) G +
      (-137) * coeff (0 + 1) G + 14 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      244 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-812) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1776) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2430 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2352 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1248) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-756) * coeff (0 + 1 + 1 + 1) G + 42 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 2 + 2 * X ^ 4 + X ^ 6 : ℚ⟦X⟧) + (-1 + 4 * X + 3 * X ^ 2 - 16 * X ^ 3 - 5 * X ^ 4 - 5 * X ^ 6 + 16 * X ^ 7 + 3 * X ^ 8 - 4 * X ^ 9 - X ^ 10 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 - 24 * X ^ 7 - 6 * X ^ 8 + 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-550) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-450) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      9720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 560 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-30450) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-7050) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      14500 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 120 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-810) * coeff (0 + 1 + 1 + 1) G + (-10) * coeff (0 + 1 + 1) G +
      (-88) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1070 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      180 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3840) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-11088) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4230) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      13830 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 2160 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2370) * coeff (0 + 1 + 1 + 1) G + (-274) * coeff (0 + 1 + 1) G +
      22 * coeff (0 + 1) G + 14 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      244 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-812) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1776) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2430 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2352 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1248) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-756) * coeff (0 + 1 + 1 + 1 + 1) G + 42 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A134424Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134424.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 10, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 + 1 + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m + 1 + 1 := rfl
  have e9 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 9 = m + 1 := rfl
  have e10 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 10 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A134424Aux.cnum 2
  have kn5 : PowerSeries.constantCoeff (5 : PowerSeries ℚ) = 5 := A134424Aux.cnum 5
  have hN1 : ((1) + (-2) * PowerSeries.X + (-5) * PowerSeries.X ^ 2 + (2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn2, kn5] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 6) * (((1) + (-2) * PowerSeries.X + (-5) * PowerSeries.X ^ 2 + (2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4) ^ 2 * ((PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 6 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 6 + 16 * PowerSeries.X ^ 7 + 3 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 4 + 24 * PowerSeries.X ^ 5 + 19 * PowerSeries.X ^ 6 - 24 * PowerSeries.X ^ 7 - 6 * PowerSeries.X ^ 8 + 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 8 + (1) * PowerSeries.X ^ 8 * T + (-4) * PowerSeries.X ^ 9 + (-5) * PowerSeries.X ^ 9 * T + (-4) * PowerSeries.X ^ 10 + (-1) * PowerSeries.X ^ 10 * T + (1) * PowerSeries.X ^ 10 * T ^ 2 + (16) * PowerSeries.X ^ 11 + (24) * PowerSeries.X ^ 11 * T + (-4) * PowerSeries.X ^ 11 * T ^ 2 + (8) * PowerSeries.X ^ 12 + (-4) * PowerSeries.X ^ 12 * T + (-4) * PowerSeries.X ^ 12 * T ^ 2 + (20) * PowerSeries.X ^ 13 + (-4) * PowerSeries.X ^ 13 * T + (16) * PowerSeries.X ^ 13 * T ^ 2 + (26) * PowerSeries.X ^ 14 + (-2) * PowerSeries.X ^ 14 * T + (8) * PowerSeries.X ^ 14 * T ^ 2 + (-20) * PowerSeries.X ^ 15 + (-66) * PowerSeries.X ^ 15 * T + (20) * PowerSeries.X ^ 15 * T ^ 2 + (8) * PowerSeries.X ^ 16 + (2) * PowerSeries.X ^ 16 * T + (26) * PowerSeries.X ^ 16 * T ^ 2 + (-16) * PowerSeries.X ^ 17 + (-4) * PowerSeries.X ^ 17 * T + (-20) * PowerSeries.X ^ 17 * T ^ 2 + (-4) * PowerSeries.X ^ 18 + (4) * PowerSeries.X ^ 18 * T + (8) * PowerSeries.X ^ 18 * T ^ 2 + (4) * PowerSeries.X ^ 19 + (24) * PowerSeries.X ^ 19 * T + (-16) * PowerSeries.X ^ 19 * T ^ 2 + (1) * PowerSeries.X ^ 20 + (1) * PowerSeries.X ^ 20 * T + (-4) * PowerSeries.X ^ 20 * T ^ 2 + (-5) * PowerSeries.X ^ 21 * T + (4) * PowerSeries.X ^ 21 * T ^ 2 + (-1) * PowerSeries.X ^ 22 * T + (1) * PowerSeries.X ^ 22 * T ^ 2) * hT +
      ((1) * PowerSeries.X ^ 6 + (-6) * PowerSeries.X ^ 7 + (-1) * PowerSeries.X ^ 8 * G + (44) * PowerSeries.X ^ 9 + (6) * PowerSeries.X ^ 9 * G + (-19) * PowerSeries.X ^ 10 + (-1) * PowerSeries.X ^ 10 * T ^ 2 + (3) * PowerSeries.X ^ 10 * G + (-100) * PowerSeries.X ^ 11 + (4) * PowerSeries.X ^ 11 * T ^ 2 + (-58) * PowerSeries.X ^ 11 * G + (9) * PowerSeries.X ^ 12 + (5) * PowerSeries.X ^ 12 * T ^ 2 + (6) * PowerSeries.X ^ 12 * G + (-20) * PowerSeries.X ^ 13 * T ^ 2 + (198) * PowerSeries.X ^ 13 * G + (9) * PowerSeries.X ^ 14 + (-13) * PowerSeries.X ^ 14 * T ^ 2 + (11) * PowerSeries.X ^ 14 * G + (100) * PowerSeries.X ^ 15 + (-198) * PowerSeries.X ^ 15 * G + (-19) * PowerSeries.X ^ 16 + (-13) * PowerSeries.X ^ 16 * T ^ 2 + (6) * PowerSeries.X ^ 16 * G + (-44) * PowerSeries.X ^ 17 + (20) * PowerSeries.X ^ 17 * T ^ 2 + (58) * PowerSeries.X ^ 17 * G + (5) * PowerSeries.X ^ 18 * T ^ 2 + (3) * PowerSeries.X ^ 18 * G + (6) * PowerSeries.X ^ 19 + (-4) * PowerSeries.X ^ 19 * T ^ 2 + (-6) * PowerSeries.X ^ 19 * G + (1) * PowerSeries.X ^ 20 + (-1) * PowerSeries.X ^ 20 * T ^ 2 + (-1) * PowerSeries.X ^ 20 * G) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 6) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 6 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 6 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 6 + 16 * PowerSeries.X ^ 7 + 3 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 4 + 24 * PowerSeries.X ^ 5 + 19 * PowerSeries.X ^ 6 - 24 * PowerSeries.X ^ 7 - 6 * PowerSeries.X ^ 8 + 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A134424Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A134424Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A134424Aux.rel G hP h0c m
      push_cast
      linear_combination r
