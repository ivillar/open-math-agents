import OMAStatements.S_oeis_a171854

-- Problem: A171854: Number of ladders in all peakless Motzkin paths of length n (n>=0).
-- Upstream: formal-conjectures statements/oeis-a171854.lean:0 (declaration OMA.S_oeis_a171854.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A171854Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X ^ 3 + 2 * X ^ 5 - X ^ 7 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G + (X ^ 2 - 2 * X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-1390 * X ^ 2 + 4884 * X ^ 3 + 60 * X ^ 4 - 5080 * X ^ 5 - 8476 * X ^ 6 - 3652 * X ^ 7 + 2878 * X ^ 8) * derivative ℚ (derivative ℚ G) + (4759 * X - 10890 * X ^ 2 - 5810 * X ^ 3 + 13574 * X ^ 4 - 10074 * X ^ 5 + 1166 * X ^ 6 + 7275 * X ^ 7) * derivative ℚ G + (17858 - 40765 * X - 14229 * X ^ 2 - 14053 * X ^ 3 + 30347 * X ^ 4 + 6109 * X ^ 5 - 7275 * X ^ 6) * G =
      23795 * X ^ 3 + 16511 * X ^ 4 - 11479 * X ^ 5 - 7275 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have hp0 : (-1 * (X * X * X) + 2 * (X * X * X * X * X) - 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * X + 2 * (X * X * X) + 2 * (X * X * X * X) - 3 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 2 * (X * X * X) - 1 * (X * X * X * X) - 2 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * (X * X * X) + 2 * (X * X * X * X * X) - 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * X + 2 * (X * X * X) + 2 * (X * X * X * X) - 3 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 2 * (X * X * X) - 1 * (X * X * X * X) - 2 * (X * X * X * X * X) + 1 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-3 * X ^ 2 + 10 * X ^ 4 - 7 * X ^ 6 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 + 6 * X ^ 2 + 8 * X ^ 3 - 18 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 6 * X ^ 2 - 4 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd1 : (-3 * X ^ 2 + 10 * X ^ 4 - 7 * X ^ 6 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 + 6 * X ^ 2 + 8 * X ^ 3 - 18 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 6 * X ^ 2 - 4 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-3 * (X * X) + 10 * (X * X * X * X) - 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * X + 2 * (X * X * X) + 2 * (X * X * X * X) - 3 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-3 + 6 * (X * X) + 8 * (X * X * X) - 18 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 4 * (X * X * X) - 2 * (X * X * X * X) - 4 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 6 * (X * X) - 4 * (X * X * X) - 10 * (X * X * X * X) + 6 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-3 * (X * X) + 10 * (X * X * X * X) - 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * X + 2 * (X * X * X) + 2 * (X * X * X * X) - 3 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-3 + 6 * (X * X) + 8 * (X * X * X) - 18 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 4 * (X * X * X) - 2 * (X * X * X * X) - 4 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 6 * (X * X) - 4 * (X * X * X) - 10 * (X * X * X * X) + 6 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-6 * X + 40 * X ^ 3 - 42 * X ^ 5 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 12 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 5 + 14 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (12 * X + 24 * X ^ 2 - 90 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 24 * X ^ 2 - 16 * X ^ 3 - 40 * X ^ 4 + 24 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 12 * X - 12 * X ^ 2 - 40 * X ^ 3 + 30 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d7, d8, d10, d18]
    ring
  have hd2 : (-6 * X + 40 * X ^ 3 - 42 * X ^ 5 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 12 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 5 + 14 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (12 * X + 24 * X ^ 2 - 90 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 24 * X ^ 2 - 16 * X ^ 3 - 40 * X ^ 4 + 24 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 12 * X - 12 * X ^ 2 - 40 * X ^ 3 + 30 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G) ^ 3 * ((-1390 * X ^ 2 + 4884 * X ^ 3 + 60 * X ^ 4 - 5080 * X ^ 5 - 8476 * X ^ 6 - 3652 * X ^ 7 + 2878 * X ^ 8) * derivative ℚ (derivative ℚ G) + (4759 * X - 10890 * X ^ 2 - 5810 * X ^ 3 + 13574 * X ^ 4 - 10074 * X ^ 5 + 1166 * X ^ 6 + 7275 * X ^ 7) * derivative ℚ G + (17858 - 40765 * X - 14229 * X ^ 2 - 14053 * X ^ 3 + 30347 * X ^ 4 + 6109 * X ^ 5 - 7275 * X ^ 6) * G - (23795 * X ^ 3 + 16511 * X ^ 4 - 11479 * X ^ 5 - 7275 * X ^ 6)) = 0 := by
    linear_combination ((17858 - 133636 * X + 290562 * X ^ 2 - 67514 * X ^ 3 - 58952 * X ^ 4 - 751490 * X ^ 5 + 28528 * X ^ 6 + 1495464 * X ^ 7 + 371468 * X ^ 8 + 465372 * X ^ 9 - 2723680 * X ^ 10 - 316196 * X ^ 11 - 861646 * X ^ 12 + 1196220 * X ^ 13 + 1037530 * X ^ 14 + 421854 * X ^ 15 + 986632 * X ^ 16 - 390010 * X ^ 17 + 340380 * X ^ 18 - 417216 * X ^ 19 + 102968 * X ^ 20 : ℚ⟦X⟧) + (82552 * X ^ 2 - 513304 * X ^ 3 + 820280 * X ^ 4 - 154304 * X ^ 5 + 1409200 * X ^ 6 - 3100560 * X ^ 7 - 888384 * X ^ 8 - 1244128 * X ^ 9 + 3074560 * X ^ 10 + 3043344 * X ^ 11 - 107280 * X ^ 12 - 85072 * X ^ 13 - 3217080 * X ^ 14 + 876664 * X ^ 15 - 752696 * X ^ 16 + 1133872 * X ^ 17 - 421152 * X ^ 18 + 43488 * X ^ 19 : ℚ⟦X⟧) * G + (82552 * X ^ 4 - 430752 * X ^ 5 + 472080 * X ^ 6 - 195528 * X ^ 7 + 2116504 * X ^ 8 - 1651664 * X ^ 9 - 228016 * X ^ 10 - 5240312 * X ^ 11 - 742104 * X ^ 12 - 2711056 * X ^ 13 + 1679872 * X ^ 14 - 374152 * X ^ 15 + 799696 * X ^ 16 - 377664 * X ^ 17 + 43488 * X ^ 18 : ℚ⟦X⟧) * G ^ 2) * hP +
      ((4759 * X - 47784 * X ^ 2 + 156685 * X ^ 3 - 101412 * X ^ 4 - 360088 * X ^ 5 + 311640 * X ^ 6 + 555463 * X ^ 7 + 421620 * X ^ 8 - 1680667 * X ^ 9 - 978848 * X ^ 10 + 1224192 * X ^ 11 + 1696760 * X ^ 12 + 433733 * X ^ 13 - 1783664 * X ^ 14 - 357049 * X ^ 15 + 383204 * X ^ 16 + 352888 * X ^ 17 - 94352 * X ^ 18 - 296899 * X ^ 19 + 192836 * X ^ 20 - 33017 * X ^ 21 : ℚ⟦X⟧) + (2780 * X ^ 4 - 23668 * X ^ 5 + 62620 * X ^ 6 - 29740 * X ^ 7 - 49852 * X ^ 8 - 100876 * X ^ 9 + 135256 * X ^ 10 + 269848 * X ^ 11 - 52968 * X ^ 12 - 240760 * X ^ 13 - 259384 * X ^ 14 + 152328 * X ^ 15 + 180812 * X ^ 16 + 26972 * X ^ 17 - 55348 * X ^ 18 - 48348 * X ^ 19 + 36084 * X ^ 20 - 5756 * X ^ 21 : ℚ⟦X⟧) * (derivative ℚ G) + (30156 * X ^ 3 - 252872 * X ^ 4 + 647516 * X ^ 5 - 220048 * X ^ 6 - 717956 * X ^ 7 - 914112 * X ^ 8 + 1326128 * X ^ 9 + 3279800 * X ^ 10 - 978064 * X ^ 11 - 2903960 * X ^ 12 - 2975984 * X ^ 13 + 1941928 * X ^ 14 + 2472740 * X ^ 15 + 162544 * X ^ 16 - 617004 * X ^ 17 - 705016 * X ^ 18 + 504468 * X ^ 19 - 80264 * X ^ 20 : ℚ⟦X⟧) * G + (5560 * X ^ 6 - 41776 * X ^ 7 + 89024 * X ^ 8 - 17792 * X ^ 9 + 13304 * X ^ 10 - 295264 * X ^ 11 + 6344 * X ^ 12 + 237472 * X ^ 13 + 433144 * X ^ 14 + 182752 * X ^ 15 - 140344 * X ^ 16 - 86080 * X ^ 17 - 47552 * X ^ 18 + 60656 * X ^ 19 - 11512 * X ^ 20 : ℚ⟦X⟧) * G * (derivative ℚ G) + (35716 * X ^ 5 - 261712 * X ^ 6 + 531432 * X ^ 7 - 51128 * X ^ 8 + 67148 * X ^ 9 - 1775952 * X ^ 10 - 168676 * X ^ 11 + 1495672 * X ^ 12 + 2586924 * X ^ 13 + 1310320 * X ^ 14 - 924868 * X ^ 15 - 492024 * X ^ 16 - 350360 * X ^ 17 + 399632 * X ^ 18 - 74508 * X ^ 19 : ℚ⟦X⟧) * G ^ 2) * hd1 +
      ((-1390 * X ^ 2 + 13224 * X ^ 3 - 41754 * X ^ 4 + 32956 * X ^ 5 + 53200 * X ^ 6 - 20668 * X ^ 7 - 128122 * X ^ 8 - 92808 * X ^ 9 + 279474 * X ^ 10 + 161192 * X ^ 11 - 152096 * X ^ 12 - 299752 * X ^ 13 - 23554 * X ^ 14 + 282776 * X ^ 15 + 55402 * X ^ 16 - 80420 * X ^ 17 - 83376 * X ^ 18 + 24420 * X ^ 19 + 39338 * X ^ 20 - 20920 * X ^ 21 + 2878 * X ^ 22 : ℚ⟦X⟧) + (-5560 * X ^ 4 + 47336 * X ^ 5 - 125240 * X ^ 6 + 59480 * X ^ 7 + 99704 * X ^ 8 + 201752 * X ^ 9 - 270512 * X ^ 10 - 539696 * X ^ 11 + 105936 * X ^ 12 + 481520 * X ^ 13 + 518768 * X ^ 14 - 304656 * X ^ 15 - 361624 * X ^ 16 - 53944 * X ^ 17 + 110696 * X ^ 18 + 96696 * X ^ 19 - 72168 * X ^ 20 + 11512 * X ^ 21 : ℚ⟦X⟧) * G + (-5560 * X ^ 6 + 41776 * X ^ 7 - 89024 * X ^ 8 + 17792 * X ^ 9 - 13304 * X ^ 10 + 295264 * X ^ 11 - 6344 * X ^ 12 - 237472 * X ^ 13 - 433144 * X ^ 14 - 182752 * X ^ 15 + 140344 * X ^ 16 + 86080 * X ^ 17 + 47552 * X ^ 18 - 60656 * X ^ 19 + 11512 * X ^ 20 : ℚ⟦X⟧) * G ^ 2) * hd2
  have hPG : (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) + (2 * X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 - 4 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X ^ 3 + 2 * X ^ 5 - X ^ 7 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G + (X ^ 2 - 2 * X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-1390) + derivative ℚ (derivative ℚ G) * X * X * X * C 4884 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 60 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-5080) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-8476) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-3652) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 2878 + derivative ℚ G * X * C 4759 +
      derivative ℚ G * X * X * C (-10890) + derivative ℚ G * X * X * X * C (-5810) +
      derivative ℚ G * X * X * X * X * C 13574 + derivative ℚ G * X * X * X * X * X * C (-10074) +
      derivative ℚ G * X * X * X * X * X * X * C 1166 + derivative ℚ G * X * X * X * X * X * X * X * C 7275 +
      G * C 17858 + G * X * C (-40765) +
      G * X * X * C (-14229) + G * X * X * X * C (-14053) +
      G * X * X * X * X * C 30347 + G * X * X * X * X * X * C 6109 +
      G * X * X * X * X * X * X * C (-7275) =
      C 23795 * X * X * X + C 16511 * X * X * X * X +
      C (-11479) * X * X * X * X * X + C (-7275) * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X ^ 3 + 2 * X ^ 5 - X ^ 7 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G + (X ^ 2 - 2 * X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-1390) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4884 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      60 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-5080) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-8476) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-3652) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      2878 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 4759 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-10890) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5810) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      13574 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-10074) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      1166 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 7275 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      17858 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-40765) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-14229) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-14053) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      30347 * coeff (m + 1 + 1 + 1 + 1) G + 6109 * coeff (m + 1 + 1 + 1) G +
      (-7275) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X ^ 3 + 2 * X ^ 5 - X ^ 7 : ℚ⟦X⟧) + (1 - 3 * X + 2 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G + (X ^ 2 - 2 * X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-58380) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 146520 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1200 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-60960) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-50856) * coeff (0 + 1 + 1 + 1) G + (-7304) * coeff (0 + 1 + 1) G +
      33313 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-65340) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-29050) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 54296 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-30222) * coeff (0 + 1 + 1 + 1) G + 2332 * coeff (0 + 1 + 1) G +
      7275 * coeff (0 + 1) G + 17858 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-40765) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-14229) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-14053) * coeff (0 + 1 + 1 + 1 + 1) G + 30347 * coeff (0 + 1 + 1 + 1) G +
      6109 * coeff (0 + 1 + 1) G + (-7275) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A171854Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a171854.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hN1 : ((1) + (-1) * PowerSeries.X ^ 2 * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 10) * (((1) + (-1) * PowerSeries.X ^ 2 * T ^ 2) ^ 2 * ((-PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 5 - PowerSeries.X ^ 7 : PowerSeries ℚ) + (1 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((-1) * PowerSeries.X ^ 12 * T ^ 2 + (-1) * PowerSeries.X ^ 13 + (-1) * PowerSeries.X ^ 13 * T + (2) * PowerSeries.X ^ 13 * T ^ 2 + (1) * PowerSeries.X ^ 14 * T + (3) * PowerSeries.X ^ 14 * T ^ 2 + (-1) * PowerSeries.X ^ 14 * T ^ 3 + (1) * PowerSeries.X ^ 14 * T ^ 4 + (2) * PowerSeries.X ^ 15 + (1) * PowerSeries.X ^ 15 * T + (-3) * PowerSeries.X ^ 15 * T ^ 2 + (2) * PowerSeries.X ^ 15 * T ^ 3 + (-2) * PowerSeries.X ^ 15 * T ^ 4 + (-2) * PowerSeries.X ^ 16 * T + (-4) * PowerSeries.X ^ 16 * T ^ 2 + (3) * PowerSeries.X ^ 16 * T ^ 3 + (-3) * PowerSeries.X ^ 16 * T ^ 4 + (-1) * PowerSeries.X ^ 17 + (1) * PowerSeries.X ^ 17 * T + (-2) * PowerSeries.X ^ 17 * T ^ 3 + (2) * PowerSeries.X ^ 17 * T ^ 4 + (1) * PowerSeries.X ^ 18 * T + (3) * PowerSeries.X ^ 18 * T ^ 2 + (-4) * PowerSeries.X ^ 18 * T ^ 3 + (4) * PowerSeries.X ^ 18 * T ^ 4 + (-1) * PowerSeries.X ^ 19 * T + (1) * PowerSeries.X ^ 19 * T ^ 2 + (-2) * PowerSeries.X ^ 19 * T ^ 3 + (2) * PowerSeries.X ^ 19 * T ^ 4 + (-1) * PowerSeries.X ^ 20 * T ^ 2 + (3) * PowerSeries.X ^ 20 * T ^ 3 + (-3) * PowerSeries.X ^ 20 * T ^ 4 + (2) * PowerSeries.X ^ 21 * T ^ 3 + (-2) * PowerSeries.X ^ 21 * T ^ 4 + (-1) * PowerSeries.X ^ 22 * T ^ 3 + (1) * PowerSeries.X ^ 22 * T ^ 4) * hT +
      ((-1) * PowerSeries.X ^ 10 + (3) * PowerSeries.X ^ 11 + (1) * PowerSeries.X ^ 12 * T ^ 2 + (-1) * PowerSeries.X ^ 12 * G + (-2) * PowerSeries.X ^ 13 + (-3) * PowerSeries.X ^ 13 * T ^ 2 + (2) * PowerSeries.X ^ 13 * G + (-2) * PowerSeries.X ^ 14 + (1) * PowerSeries.X ^ 14 * T ^ 2 + (-1) * PowerSeries.X ^ 14 * T ^ 3 + (1) * PowerSeries.X ^ 14 * G + (1) * PowerSeries.X ^ 14 * G * T ^ 2 + (2) * PowerSeries.X ^ 15 * T ^ 3 + (2) * PowerSeries.X ^ 15 * G + (-2) * PowerSeries.X ^ 15 * G * T ^ 2 + (3) * PowerSeries.X ^ 16 + (2) * PowerSeries.X ^ 16 * T ^ 3 + (-1) * PowerSeries.X ^ 16 * G + (-1) * PowerSeries.X ^ 16 * G * T ^ 2 + (-1) * PowerSeries.X ^ 17 + (-2) * PowerSeries.X ^ 17 * G * T ^ 2 + (-1) * PowerSeries.X ^ 18 * T ^ 2 + (-2) * PowerSeries.X ^ 18 * T ^ 3 + (1) * PowerSeries.X ^ 18 * G * T ^ 2 + (3) * PowerSeries.X ^ 19 * T ^ 2 + (-2) * PowerSeries.X ^ 19 * T ^ 3 + (-1) * PowerSeries.X ^ 20 * T ^ 2 + (1) * PowerSeries.X ^ 20 * T ^ 3) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 10) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 10 PowerSeries.X_ne_zero)
  have hP : (-PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 5 - PowerSeries.X ^ 7 : PowerSeries ℚ) + (1 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A171854Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A171854Aux.rel G hP h0c m
    push_cast
    linear_combination r
