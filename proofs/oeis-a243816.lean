import OMAStatements.S_oeis_a243816

-- Problem: A243816: Expansion of (x*sqrt(4*x^2+1)-x)/(x*sqrt(-(2*sqrt(4*x^2+1)-x-2)/x) + sqrt(4*x^2+1)-x-1).
-- Upstream: formal-conjectures statements/oeis-a243816.lean:0 (declaration OMA.S_oeis_a243816.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243816Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    (4 * X ^ 3 - 47 * X ^ 4 + 152 * X ^ 5 - 376 * X ^ 6 + 1024 * X ^ 7 - 752 * X ^ 8 + 1920 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2 * X ^ 2 - 14 * X ^ 3 + 168 * X ^ 4 - 488 * X ^ 5 + 2080 * X ^ 6 - 1728 * X ^ 7 + 5760 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-6 * X ^ 2 - 4 * X ^ 3 - 212 * X ^ 4 + 400 * X ^ 5) * derivative ℚ G + (-8 * X ^ 2 + 80 * X ^ 3 - 400 * X ^ 4) * G =
      -4 * X ^ 2 - 32 * X ^ 3 - 32 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d40 : derivative ℚ (40 : ℚ⟦X⟧) = 0 := dnum 40
  have hp0 : (1 * (X * X * X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * G + (-2 * X + 5 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X * X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * G + (-2 * X + 5 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (4 * X ^ 3 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-2 + 10 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d5]
    ring
  have hd1 : (4 * X ^ 3 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * X ^ 2 : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-2 + 10 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (4 * (X * X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * (X * X) : ℚ⟦X⟧) * G + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-2 + 10 * X : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 12 * (X * X) : ℚ⟦X⟧) * G + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-2 + 10 * X : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 * X - 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 24 * X : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-8 + 40 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (10 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d3, d4, d10, d12]
    ring
  have hd2 : (12 * X ^ 2 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 * X - 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 24 * X : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-8 + 40 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (10 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (12 * (X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 * X - 24 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 - 24 * X : ℚ⟦X⟧) * G + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-8 + 40 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (10 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((12 * (X * X) : ℚ⟦X⟧) + (1 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (4 * X - 24 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 - 24 * X : ℚ⟦X⟧) * G + (-4 * X + 10 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-8 + 40 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (10 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (24 * X : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 * X - 36 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 - 72 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X + 30 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-12 + 60 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-24 : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 + 60 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (60 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d10, d12, d24, d40]
    ring
  have hd3 : (24 * X : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 * X - 36 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 - 72 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X + 30 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-12 + 60 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-24 : ℚ⟦X⟧) * G + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 + 60 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (60 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((4 * X ^ 3 - 47 * X ^ 4 + 152 * X ^ 5 - 376 * X ^ 6 + 1024 * X ^ 7 - 752 * X ^ 8 + 1920 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2 * X ^ 2 - 14 * X ^ 3 + 168 * X ^ 4 - 488 * X ^ 5 + 2080 * X ^ 6 - 1728 * X ^ 7 + 5760 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-6 * X ^ 2 - 4 * X ^ 3 - 212 * X ^ 4 + 400 * X ^ 5) * derivative ℚ G + (-8 * X ^ 2 + 80 * X ^ 3 - 400 * X ^ 4) * G - (-4 * X ^ 2 - 32 * X ^ 3 - 32 * X ^ 4)) = 0 := by
    linear_combination ((-84 * X ^ 8 + 1176 * X ^ 9 - 5312 * X ^ 10 + 11856 * X ^ 11 + 20800 * X ^ 12 - 225152 * X ^ 13 + 733440 * X ^ 14 - 2420224 * X ^ 15 + 4691968 * X ^ 16 - 6303744 * X ^ 17 + 7372800 * X ^ 18 : ℚ⟦X⟧) + (120 * X ^ 7 - 2024 * X ^ 8 - 120 * X ^ 9 + 108896 * X ^ 10 - 744192 * X ^ 11 + 2748800 * X ^ 12 - 7337984 * X ^ 13 + 18818048 * X ^ 14 - 37019648 * X ^ 15 + 44630016 * X ^ 16 - 50135040 * X ^ 17 : ℚ⟦X⟧) * G + (468 * X ^ 6 - 5248 * X ^ 7 + 60344 * X ^ 8 - 491480 * X ^ 9 + 2061440 * X ^ 10 - 4831104 * X ^ 11 + 9415040 * X ^ 12 - 27277312 * X ^ 13 + 71037952 * X ^ 14 - 86679552 * X ^ 15 + 99532800 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (-1392 * X ^ 5 + 15472 * X ^ 6 - 82224 * X ^ 7 + 187072 * X ^ 8 + 1322496 * X ^ 9 - 13476096 * X ^ 10 + 49291008 * X ^ 11 - 80956416 * X ^ 12 + 48547840 * X ^ 13 - 24551424 * X ^ 14 - 5898240 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (1428 * X ^ 4 - 11880 * X ^ 5 - 60848 * X ^ 6 + 1513024 * X ^ 7 - 12210624 * X ^ 8 + 59848320 * X ^ 9 - 187426816 * X ^ 10 + 341983104 * X ^ 11 - 364834816 * X ^ 12 + 321733632 * X ^ 13 - 263946240 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (-648 * X ^ 3 + 1976 * X ^ 4 + 180648 * X ^ 5 - 2773664 * X ^ 6 + 20733056 * X ^ 7 - 97258880 * X ^ 8 + 302850432 * X ^ 9 - 572315136 * X ^ 10 + 624454656 * X ^ 11 - 533839872 * X ^ 12 + 489553920 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (108 * X ^ 2 - 48 * X ^ 3 - 118824 * X ^ 4 + 2150024 * X ^ 5 - 17950784 * X ^ 6 + 90229376 * X ^ 7 - 293965696 * X ^ 8 + 577328384 * X ^ 9 - 603159552 * X ^ 10 + 430768128 * X ^ 11 - 459325440 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (576 * X ^ 2 + 24320 * X ^ 3 - 813440 * X ^ 4 + 8885376 * X ^ 5 - 52612096 * X ^ 6 + 189359104 * X ^ 7 - 395761664 * X ^ 8 + 390029312 * X ^ 9 - 166969344 * X ^ 10 + 235929600 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-1056 * X ^ 2 + 151232 * X ^ 3 - 2561472 * X ^ 4 + 19697664 * X ^ 5 - 84712448 * X ^ 6 + 197343232 * X ^ 7 - 193878016 * X ^ 8 + 13529088 * X ^ 9 - 50135040 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-11776 * X ^ 2 + 405504 * X ^ 3 - 4493312 * X ^ 4 + 25454592 * X ^ 5 - 72622080 * X ^ 6 + 79855616 * X ^ 7 + 7127040 * X ^ 8 - 5898240 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (-26624 * X ^ 2 + 540672 * X ^ 3 - 4429824 * X ^ 4 + 17725440 * X ^ 5 - 25149440 * X ^ 6 - 884736 * X ^ 7 + 2949120 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (-24576 * X ^ 2 + 344064 * X ^ 3 - 2211840 * X ^ 4 + 4915200 * X ^ 5 : ℚ⟦X⟧) * G ^ 11 + (-8192 * X ^ 2 + 81920 * X ^ 3 - 409600 * X ^ 4 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((64 * X ^ 9 - 1644 * X ^ 10 + 18460 * X ^ 11 - 120204 * X ^ 12 + 487792 * X ^ 13 - 1374624 * X ^ 14 + 3054080 * X ^ 15 - 5222272 * X ^ 16 + 6399488 * X ^ 17 - 5932032 * X ^ 18 + 4055040 * X ^ 19 : ℚ⟦X⟧) + (-232 * X ^ 9 + 5912 * X ^ 10 - 62932 * X ^ 11 + 379064 * X ^ 12 - 1488032 * X ^ 13 + 4254144 * X ^ 14 - 9630976 * X ^ 15 + 17136768 * X ^ 16 - 22646528 * X ^ 17 + 23227392 * X ^ 18 - 15851520 * X ^ 19 : ℚ⟦X⟧) * (derivative ℚ G) + (168 * X ^ 9 - 4086 * X ^ 10 + 40848 * X ^ 11 - 228228 * X ^ 12 + 842304 * X ^ 13 - 2347584 * X ^ 14 + 5212416 * X ^ 15 - 8871744 * X ^ 16 + 11510784 * X ^ 17 - 11486208 * X ^ 18 + 6266880 * X ^ 19 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-384 * X ^ 8 + 12944 * X ^ 9 - 162964 * X ^ 10 + 1069552 * X ^ 11 - 4259872 * X ^ 12 + 11798016 * X ^ 13 - 25686976 * X ^ 14 + 43008512 * X ^ 15 - 50149376 * X ^ 16 + 46685184 * X ^ 17 - 30597120 * X ^ 18 : ℚ⟦X⟧) * G + (2292 * X ^ 8 - 58548 * X ^ 9 + 616752 * X ^ 10 - 3636144 * X ^ 11 + 13928496 * X ^ 12 - 39141120 * X ^ 13 + 87338880 * X ^ 14 - 152161920 * X ^ 15 + 198332160 * X ^ 16 - 200114688 * X ^ 17 + 131788800 * X ^ 18 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1824 * X ^ 8 + 43176 * X ^ 9 - 420996 * X ^ 10 + 2315568 * X ^ 11 - 8506224 * X ^ 12 + 23676864 * X ^ 13 - 52387008 * X ^ 14 + 89320704 * X ^ 15 - 116237568 * X ^ 16 + 115596288 * X ^ 17 - 65249280 * X ^ 18 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (1272 * X ^ 7 - 50074 * X ^ 8 + 664576 * X ^ 9 - 4404444 * X ^ 10 + 17468432 * X ^ 11 - 48179616 * X ^ 12 + 104198016 * X ^ 13 - 172916800 * X ^ 14 + 198526208 * X ^ 15 - 184177152 * X ^ 16 + 129024000 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (-9288 * X ^ 7 + 241980 * X ^ 8 - 2565996 * X ^ 9 + 15074736 * X ^ 10 - 57286008 * X ^ 11 + 159671904 * X ^ 12 - 353526528 * X ^ 13 + 610705920 * X ^ 14 - 788307840 * X ^ 15 + 790909440 * X ^ 16 - 515727360 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (7896 * X ^ 7 - 186858 * X ^ 8 + 1828272 * X ^ 9 - 10131312 * X ^ 10 + 37511232 * X ^ 11 - 104945520 * X ^ 12 + 233437056 * X ^ 13 - 401096832 * X ^ 14 + 524888064 * X ^ 15 - 525827328 * X ^ 16 + 305326080 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-2824 * X ^ 6 + 115864 * X ^ 7 - 1580592 * X ^ 8 + 10722512 * X ^ 9 - 43089824 * X ^ 10 + 119111328 * X ^ 11 - 257725952 * X ^ 12 + 426358272 * X ^ 13 - 483845632 * X ^ 14 + 442821120 * X ^ 15 - 340623360 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 + (19828 * X ^ 6 - 538388 * X ^ 7 + 5892568 * X ^ 8 - 35367032 * X ^ 9 + 135637136 * X ^ 10 - 378165648 * X ^ 11 + 837783040 * X ^ 12 - 1449985920 * X ^ 13 + 1865178368 * X ^ 14 - 1874956032 * X ^ 15 + 1248768000 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-17472 * X ^ 6 + 428496 * X ^ 7 - 4352136 * X ^ 8 + 24901152 * X ^ 9 - 94246848 * X ^ 10 + 267340800 * X ^ 11 - 603182208 * X ^ 12 + 1053166080 * X ^ 13 - 1393391616 * X ^ 14 + 1419190272 * X ^ 15 - 858193920 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (3696 * X ^ 5 - 160566 * X ^ 6 + 2309536 * X ^ 7 - 16439752 * X ^ 8 + 68135712 * X ^ 9 - 189902176 * X ^ 10 + 410700864 * X ^ 11 - 678111424 * X ^ 12 + 745518848 * X ^ 13 - 653952000 * X ^ 14 + 564848640 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (-23256 * X ^ 5 + 688800 * X ^ 6 - 8107692 * X ^ 7 + 51358320 * X ^ 8 - 202872648 * X ^ 9 + 570766176 * X ^ 10 - 1274548224 * X ^ 11 + 2233202688 * X ^ 12 - 2875643520 * X ^ 13 + 2911151616 * X ^ 14 - 2041896960 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (20952 * X ^ 5 - 558954 * X ^ 6 + 6149232 * X ^ 7 - 37471068 * X ^ 8 + 147689280 * X ^ 9 - 429178752 * X ^ 10 + 991938816 * X ^ 11 - 1777910976 * X ^ 12 + 2393809920 * X ^ 13 - 2499840000 * X ^ 14 + 1603584000 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-2256 * X ^ 4 + 124008 * X ^ 5 - 2040564 * X ^ 6 + 15895440 * X ^ 7 - 69693168 * X ^ 8 + 197687712 * X ^ 9 - 424523712 * X ^ 10 + 696462336 * X ^ 11 - 708347136 * X ^ 12 + 537911808 * X ^ 13 - 575447040 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 + (13788 * X ^ 4 - 495156 * X ^ 5 + 6734976 * X ^ 6 - 47163048 * X ^ 7 + 197265936 * X ^ 8 - 565841280 * X ^ 9 + 1278916992 * X ^ 10 - 2294449920 * X ^ 11 + 2965179648 * X ^ 12 - 3016014336 * X ^ 13 + 2313031680 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-12960 * X ^ 4 + 409608 * X ^ 5 - 5193972 * X ^ 6 + 35215056 * X ^ 7 - 148496256 * X ^ 8 + 447887232 * X ^ 9 - 1071508032 * X ^ 10 + 1997634816 * X ^ 11 - 2757312000 * X ^ 12 + 2973247488 * X ^ 13 - 2072494080 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (216 * X ^ 3 - 43694 * X ^ 4 + 1008440 * X ^ 5 - 9339076 * X ^ 6 + 45106096 * X ^ 7 - 132149088 * X ^ 8 + 277717504 * X ^ 9 - 440029888 * X ^ 10 + 361188096 * X ^ 11 - 105297408 * X ^ 12 + 291594240 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (-2808 * X ^ 3 + 174372 * X ^ 4 - 3182412 * X ^ 5 + 26678760 * X ^ 6 - 123372720 * X ^ 7 + 365683392 * X ^ 8 - 834263040 * X ^ 9 + 1548443520 * X ^ 10 - 2010347520 * X ^ 11 + 2005641216 * X ^ 12 - 1777213440 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (3240 * X ^ 3 - 152118 * X ^ 4 + 2492688 * X ^ 5 - 20178768 * X ^ 6 + 95017728 * X ^ 7 - 303065184 * X ^ 8 + 757812480 * X ^ 9 - 1494882816 * X ^ 10 + 2135629824 * X ^ 11 - 2382987264 * X ^ 12 + 1863843840 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (216 * X ^ 2 + 2064 * X ^ 3 - 228056 * X ^ 4 + 3044000 * X ^ 5 - 17431744 * X ^ 6 + 54181824 * X ^ 7 - 107686912 * X ^ 8 + 146347264 * X ^ 9 - 24482816 * X ^ 10 - 248469504 * X ^ 11 + 57139200 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (-324 * X ^ 2 - 17028 * X ^ 3 + 716424 * X ^ 4 - 8544960 * X ^ 5 + 47273472 * X ^ 6 - 147961152 * X ^ 7 + 333222528 * X ^ 8 - 641176320 * X ^ 9 + 834140160 * X ^ 10 - 739845120 * X ^ 11 + 846766080 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (20736 * X ^ 3 - 593856 * X ^ 4 + 6566400 * X ^ 5 - 37180800 * X ^ 6 + 129378816 * X ^ 7 - 340273152 * X ^ 8 + 725151744 * X ^ 9 - 1089533952 * X ^ 10 + 1245487104 * X ^ 11 - 1141309440 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (1098 * X ^ 2 + 11164 * X ^ 3 - 463276 * X ^ 4 + 3620912 * X ^ 5 - 12563328 * X ^ 6 + 22327808 * X ^ 7 - 10326656 * X ^ 8 - 79894016 * X ^ 9 + 266489856 * X ^ 10 - 194273280 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (-1944 * X ^ 2 - 38136 * X ^ 3 + 1263504 * X ^ 4 - 9983232 * X ^ 5 + 34483200 * X ^ 6 - 70311168 * X ^ 7 + 132213504 * X ^ 8 - 168190464 * X ^ 9 + 58484736 * X ^ 10 - 176947200 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (50112 * X ^ 3 - 1045008 * X ^ 4 + 8204544 * X ^ 5 - 33091200 * X ^ 6 + 91431936 * X ^ 7 - 214569216 * X ^ 8 + 350466048 * X ^ 9 - 395698176 * X ^ 10 + 451215360 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (1344 * X ^ 2 + 22560 * X ^ 3 - 332480 * X ^ 4 + 1348096 * X ^ 5 - 2486272 * X ^ 6 - 5757952 * X ^ 7 + 44228608 * X ^ 8 - 116496384 * X ^ 9 + 128286720 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (-4320 * X ^ 2 - 30688 * X ^ 3 + 875840 * X ^ 4 - 3753472 * X ^ 5 + 4218880 * X ^ 6 + 104448 * X ^ 7 - 6446080 * X ^ 8 + 58509312 * X ^ 9 - 36126720 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (53760 * X ^ 3 - 846720 * X ^ 4 + 4569600 * X ^ 5 - 13224960 * X ^ 6 + 33976320 * X ^ 7 - 65157120 * X ^ 8 + 66232320 * X ^ 9 - 103219200 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-1088 * X ^ 2 + 18816 * X ^ 3 - 23808 * X ^ 4 + 324096 * X ^ 5 - 204800 * X ^ 6 - 9179136 * X ^ 7 + 22419456 * X ^ 8 - 38338560 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (-4224 * X ^ 2 + 3456 * X ^ 3 + 32256 * X ^ 4 + 815616 * X ^ 5 - 4472832 * X ^ 6 + 10211328 * X ^ 7 - 18677760 * X ^ 8 + 28016640 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (21504 * X ^ 3 - 252672 * X ^ 4 + 817152 * X ^ 5 - 2021376 * X ^ 6 + 5505024 * X ^ 7 - 4042752 * X ^ 8 + 10321920 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (-3072 * X ^ 2 + 4608 * X ^ 3 - 21504 * X ^ 4 + 583680 * X ^ 5 + 368640 * X ^ 6 - 1327104 * X ^ 7 + 4423680 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (-1536 * X ^ 2 + 10752 * X ^ 3 - 129024 * X ^ 4 + 374784 * X ^ 5 - 1597440 * X ^ 6 + 1327104 * X ^ 7 - 4423680 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-1536 * X ^ 2 - 1024 * X ^ 3 - 54272 * X ^ 4 + 102400 * X ^ 5 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-22 * X ^ 10 + 668 * X ^ 11 - 8284 * X ^ 12 + 55928 * X ^ 13 - 234560 * X ^ 14 + 686688 * X ^ 15 - 1573312 * X ^ 16 + 2862336 * X ^ 17 - 3802112 * X ^ 18 + 3870720 * X ^ 19 - 2949120 * X ^ 20 : ℚ⟦X⟧) + (48 * X ^ 10 - 1260 * X ^ 11 + 13746 * X ^ 12 - 83784 * X ^ 13 + 331440 * X ^ 14 - 964992 * X ^ 15 + 2234400 * X ^ 16 - 4020864 * X ^ 17 + 5423616 * X ^ 18 - 5683200 * X ^ 19 + 3686400 * X ^ 20 : ℚ⟦X⟧) * (derivative ℚ G) + (304 * X ^ 9 - 8828 * X ^ 10 + 103456 * X ^ 11 - 657272 * X ^ 12 + 2609600 * X ^ 13 - 7355136 * X ^ 14 + 16390912 * X ^ 15 - 28692864 * X ^ 16 + 36804608 * X ^ 17 - 36894720 * X ^ 18 + 25804800 * X ^ 19 : ℚ⟦X⟧) * G + (-648 * X ^ 9 + 16254 * X ^ 10 - 168912 * X ^ 11 + 985068 * X ^ 12 - 3775680 * X ^ 13 + 10793088 * X ^ 14 - 24544512 * X ^ 15 + 43222464 * X ^ 16 - 57535488 * X ^ 17 + 59083776 * X ^ 18 - 36495360 * X ^ 19 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1728 * X ^ 8 + 48690 * X ^ 9 - 547704 * X ^ 10 + 3336336 * X ^ 11 - 12787056 * X ^ 12 + 35160480 * X ^ 13 - 76674816 * X ^ 14 + 130763520 * X ^ 15 - 164088576 * X ^ 16 + 161547264 * X ^ 17 - 109486080 * X ^ 18 : ℚ⟦X⟧) * G ^ 2 + (3600 * X ^ 8 - 87732 * X ^ 9 + 885762 * X ^ 10 - 5046840 * X ^ 11 + 19064520 * X ^ 12 - 54025632 * X ^ 13 + 121738464 * X ^ 14 - 212416128 * X ^ 15 + 280957824 * X ^ 16 - 285792768 * X ^ 17 + 173076480 * X ^ 18 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (5200 * X ^ 7 - 145668 * X ^ 8 + 1611956 * X ^ 9 - 9647432 * X ^ 10 + 36367264 * X ^ 11 - 98414112 * X ^ 12 + 211318336 * X ^ 13 - 354822016 * X ^ 14 + 437346304 * X ^ 15 - 424806912 * X ^ 16 + 288460800 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 + (-10632 * X ^ 7 + 258174 * X ^ 8 - 2601552 * X ^ 9 + 14826720 * X ^ 10 - 56065344 * X ^ 11 + 158966832 * X ^ 12 - 358447488 * X ^ 13 + 626144640 * X ^ 14 - 828831744 * X ^ 15 + 843926784 * X ^ 16 - 513239040 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-8860 * X ^ 6 + 256874 * X ^ 7 - 2899288 * X ^ 8 + 17551112 * X ^ 9 - 66226208 * X ^ 10 + 177606624 * X ^ 11 - 377394688 * X ^ 12 + 628610304 * X ^ 13 - 761555456 * X ^ 14 + 730246656 * X ^ 15 - 513239040 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 + (18000 * X ^ 6 - 451620 * X ^ 7 + 4702050 * X ^ 8 - 27519480 * X ^ 9 + 105882840 * X ^ 10 - 303400800 * X ^ 11 + 691463520 * X ^ 12 - 1221886080 * X ^ 13 + 1630016640 * X ^ 14 - 1678763520 * X ^ 15 + 1047859200 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (8400 * X ^ 5 - 270180 * X ^ 6 + 3278904 * X ^ 7 - 20802120 * X ^ 8 + 80140656 * X ^ 9 - 214162272 * X ^ 10 + 450914304 * X ^ 11 - 748714368 * X ^ 12 + 886285056 * X ^ 13 - 830430720 * X ^ 14 + 628715520 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 + (-17496 * X ^ 5 + 478026 * X ^ 6 - 5378544 * X ^ 7 + 33394068 * X ^ 8 - 133357248 * X ^ 9 + 390543552 * X ^ 10 - 909105408 * X ^ 11 + 1643807808 * X ^ 12 - 2226207744 * X ^ 13 + 2341380096 * X ^ 14 - 1535016960 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-3888 * X ^ 4 + 160870 * X ^ 5 - 2287288 * X ^ 6 + 15996888 * X ^ 7 - 64609904 * X ^ 8 + 172637280 * X ^ 9 - 357380352 * X ^ 10 + 590954368 * X ^ 11 - 669072128 * X ^ 12 + 584239104 * X ^ 13 - 511672320 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 + (9072 * X ^ 4 - 295596 * X ^ 5 + 3833550 * X ^ 6 - 26414136 * X ^ 7 + 112563360 * X ^ 8 - 341498304 * X ^ 9 + 820909152 * X ^ 10 - 1539780480 * X ^ 11 + 2134008576 * X ^ 12 - 2309981184 * X ^ 13 + 1633443840 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (432 * X ^ 3 - 45180 * X ^ 4 + 907860 * X ^ 5 - 7648200 * X ^ 6 + 33774048 * X ^ 7 - 90231360 * X ^ 8 + 177448512 * X ^ 9 - 285684864 * X ^ 10 + 285739008 * X ^ 11 - 176956416 * X ^ 12 + 233349120 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 + (-1944 * X ^ 3 + 95418 * X ^ 4 - 1599408 * X ^ 5 + 13131216 * X ^ 6 - 62348544 * X ^ 7 + 199682208 * X ^ 8 - 500758272 * X ^ 9 + 991586304 * X ^ 10 - 1420296192 * X ^ 11 + 1587400704 * X ^ 12 - 1251901440 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (162 * X ^ 2 + 1890 * X ^ 3 - 162780 * X ^ 4 + 2047608 * X ^ 5 - 10714752 * X ^ 6 + 28394688 * X ^ 7 - 46154688 * X ^ 8 + 60999168 * X ^ 9 - 23642112 * X ^ 10 - 79755264 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (-11664 * X ^ 3 + 339228 * X ^ 4 - 3789936 * X ^ 5 + 21586176 * X ^ 6 - 75299328 * X ^ 7 + 198293184 * X ^ 8 - 423463680 * X ^ 9 + 637051392 * X ^ 10 - 728635392 * X ^ 11 + 670187520 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (864 * X ^ 2 + 1440 * X ^ 3 - 230416 * X ^ 4 + 1779008 * X ^ 5 - 4461568 * X ^ 6 + 1160704 * X ^ 7 + 12258048 * X ^ 8 - 42345472 * X ^ 9 + 105449472 * X ^ 10 - 74465280 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-25920 * X ^ 3 + 542640 * X ^ 4 - 4273920 * X ^ 5 + 17258880 * X ^ 6 - 47692800 * X ^ 7 + 112024320 * X ^ 8 - 183029760 * X ^ 9 + 206684160 * X ^ 10 - 235929600 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (1728 * X ^ 2 - 4160 * X ^ 3 - 89024 * X ^ 4 + 75520 * X ^ 5 + 2448896 * X ^ 6 - 10659840 * X ^ 7 + 23127040 * X ^ 8 - 44113920 * X ^ 9 + 47185920 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-25344 * X ^ 3 + 399168 * X ^ 4 - 2154240 * X ^ 5 + 6234624 * X ^ 6 - 16017408 * X ^ 7 + 30716928 * X ^ 8 - 31223808 * X ^ 9 + 48660480 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (1536 * X ^ 2 - 7680 * X ^ 3 + 63744 * X ^ 4 - 540672 * X ^ 5 + 2230272 * X ^ 6 - 5357568 * X ^ 7 + 7999488 * X ^ 8 - 13271040 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (-9216 * X ^ 3 + 108288 * X ^ 4 - 350208 * X ^ 5 + 866304 * X ^ 6 - 2359296 * X ^ 7 + 1732608 * X ^ 8 - 4423680 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (512 * X ^ 2 - 3584 * X ^ 3 + 43008 * X ^ 4 - 124928 * X ^ 5 + 532480 * X ^ 6 - 442368 * X ^ 7 + 1474560 * X ^ 8 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((4 * X ^ 11 - 111 * X ^ 12 + 1288 * X ^ 13 - 8344 * X ^ 14 + 34688 * X ^ 15 - 104176 * X ^ 16 + 247424 * X ^ 17 - 461312 * X ^ 18 + 638976 * X ^ 19 - 684032 * X ^ 20 + 491520 * X ^ 21 : ℚ⟦X⟧) + (-64 * X ^ 10 + 1680 * X ^ 11 - 18328 * X ^ 12 + 111712 * X ^ 13 - 441920 * X ^ 14 + 1286656 * X ^ 15 - 2979200 * X ^ 16 + 5361152 * X ^ 17 - 7231488 * X ^ 18 + 7577600 * X ^ 19 - 4915200 * X ^ 20 : ℚ⟦X⟧) * G + (432 * X ^ 9 - 10836 * X ^ 10 + 112608 * X ^ 11 - 656712 * X ^ 12 + 2517120 * X ^ 13 - 7195392 * X ^ 14 + 16363008 * X ^ 15 - 28814976 * X ^ 16 + 38356992 * X ^ 17 - 39389184 * X ^ 18 + 24330240 * X ^ 19 : ℚ⟦X⟧) * G ^ 2 + (-1600 * X ^ 8 + 38992 * X ^ 9 - 393672 * X ^ 10 + 2243040 * X ^ 11 - 8473120 * X ^ 12 + 24011392 * X ^ 13 - 54105984 * X ^ 14 + 94407168 * X ^ 15 - 124870144 * X ^ 16 + 127019008 * X ^ 17 - 76922880 * X ^ 18 : ℚ⟦X⟧) * G ^ 3 + (3544 * X ^ 7 - 86058 * X ^ 8 + 867184 * X ^ 9 - 4942240 * X ^ 10 + 18688448 * X ^ 11 - 52988944 * X ^ 12 + 119482496 * X ^ 13 - 208714880 * X ^ 14 + 276277248 * X ^ 15 - 281308928 * X ^ 16 + 171079680 * X ^ 17 : ℚ⟦X⟧) * G ^ 4 + (-4800 * X ^ 6 + 120432 * X ^ 7 - 1253880 * X ^ 8 + 7338528 * X ^ 9 - 28235424 * X ^ 10 + 80906880 * X ^ 11 - 184390272 * X ^ 12 + 325836288 * X ^ 13 - 434671104 * X ^ 14 + 447670272 * X ^ 15 - 279429120 * X ^ 16 : ℚ⟦X⟧) * G ^ 5 + (3888 * X ^ 5 - 106228 * X ^ 6 + 1195232 * X ^ 7 - 7420904 * X ^ 8 + 29634944 * X ^ 9 - 86787456 * X ^ 10 + 202023424 * X ^ 11 - 365290624 * X ^ 12 + 494712832 * X ^ 13 - 520306688 * X ^ 14 + 341114880 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 + (-1728 * X ^ 4 + 56304 * X ^ 5 - 730200 * X ^ 6 + 5031264 * X ^ 7 - 21440640 * X ^ 8 + 65047296 * X ^ 9 - 156363648 * X ^ 10 + 293291520 * X ^ 11 - 406477824 * X ^ 12 + 439996416 * X ^ 13 - 311132160 * X ^ 14 : ℚ⟦X⟧) * G ^ 7 + (324 * X ^ 3 - 15903 * X ^ 4 + 266568 * X ^ 5 - 2188536 * X ^ 6 + 10391424 * X ^ 7 - 33280368 * X ^ 8 + 83459712 * X ^ 9 - 165264384 * X ^ 10 + 236716032 * X ^ 11 - 264566784 * X ^ 12 + 208650240 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (1728 * X ^ 3 - 50256 * X ^ 4 + 561472 * X ^ 5 - 3197952 * X ^ 6 + 11155456 * X ^ 7 - 29376768 * X ^ 8 + 62735360 * X ^ 9 - 94377984 * X ^ 10 + 107945984 * X ^ 11 - 99287040 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (3456 * X ^ 3 - 72352 * X ^ 4 + 569856 * X ^ 5 - 2301184 * X ^ 6 + 6359040 * X ^ 7 - 14936576 * X ^ 8 + 24403968 * X ^ 9 - 27557888 * X ^ 10 + 31457280 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (3072 * X ^ 3 - 48384 * X ^ 4 + 261120 * X ^ 5 - 755712 * X ^ 6 + 1941504 * X ^ 7 - 3723264 * X ^ 8 + 3784704 * X ^ 9 - 5898240 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (1024 * X ^ 3 - 12032 * X ^ 4 + 38912 * X ^ 5 - 96256 * X ^ 6 + 262144 * X ^ 7 - 192512 * X ^ 8 + 491520 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) + (-4 * X + 10 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k4] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 4 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-47) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 152 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-376) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 1024 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C (-752) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C 1920 + derivative ℚ (derivative ℚ G) * X * X * C 2 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-14) + derivative ℚ (derivative ℚ G) * X * X * X * X * C 168 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-488) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 2080 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-1728) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 5760 +
      derivative ℚ G * X * X * C (-6) + derivative ℚ G * X * X * X * C (-4) +
      derivative ℚ G * X * X * X * X * C (-212) + derivative ℚ G * X * X * X * X * X * C 400 +
      G * X * X * C (-8) + G * X * X * X * C 80 +
      G * X * X * X * X * C (-400) =
      C (-4) * X * X + C (-32) * X * X * X +
      C (-32) * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-47) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      152 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-376) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      1024 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-752) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      1920 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 2 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-14) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 168 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-488) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 2080 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-1728) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 5760 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-6) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-212) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 400 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 80 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-400) * coeff (m + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    480 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2820) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      3648 * coeff (0 + 1 + 1 + 1 + 1) G + (-2256) * coeff (0 + 1 + 1 + 1) G +
      60 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-280) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2016 * coeff (0 + 1 + 1 + 1 + 1) G + (-2928) * coeff (0 + 1 + 1 + 1) G +
      4160 * coeff (0 + 1 + 1) G + (-30) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-16) * coeff (0 + 1 + 1 + 1 + 1) G + (-636) * coeff (0 + 1 + 1 + 1) G +
      800 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      80 * coeff (0 + 1 + 1 + 1) G + (-400) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    840 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5640) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      9120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-9024) * coeff (0 + 1 + 1 + 1 + 1) G +
      6144 * coeff (0 + 1 + 1 + 1) G + 84 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-420) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 3360 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-5856) * coeff (0 + 1 + 1 + 1 + 1) G + 12480 * coeff (0 + 1 + 1 + 1) G +
      (-3456) * coeff (0 + 1 + 1) G + (-36) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-20) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-848) * coeff (0 + 1 + 1 + 1 + 1) G +
      1200 * coeff (0 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      80 * coeff (0 + 1 + 1 + 1 + 1) G + (-400) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (-2 * X + 5 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    1344 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9870) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      18240 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22560) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      24576 * coeff (0 + 1 + 1 + 1 + 1) G + (-4512) * coeff (0 + 1 + 1 + 1) G +
      112 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-588) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      5040 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9760) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      24960 * coeff (0 + 1 + 1 + 1 + 1) G + (-10368) * coeff (0 + 1 + 1 + 1) G +
      11520 * coeff (0 + 1 + 1) G + (-42) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-24) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1060) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      1600 * coeff (0 + 1 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      80 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-400) * coeff (0 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243816Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243816.main := by
  intro T U G hT _ hU _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hn : ((-1) + (1) * T + (-1) * PowerSeries.X + (1) * PowerSeries.X * U) * ((-1) * PowerSeries.X ^ 2 + (-1) * PowerSeries.X ^ 2 * T + (1) * PowerSeries.X ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 2 * T ^ 3 + (-1) * PowerSeries.X ^ 3 + (-1) * PowerSeries.X ^ 3 * U + (-2) * PowerSeries.X ^ 3 * T + (-2) * PowerSeries.X ^ 3 * T * U + (-1) * PowerSeries.X ^ 3 * T ^ 2 + (-1) * PowerSeries.X ^ 3 * T ^ 2 * U) = (16 * PowerSeries.X ^ 6 : PowerSeries ℚ) := by
    linear_combination ((-1) * PowerSeries.X ^ 2 + (1) * PowerSeries.X ^ 2 * T ^ 2 + (4) * PowerSeries.X ^ 4) * hT + ((-1) * PowerSeries.X ^ 3 + (-2) * PowerSeries.X ^ 3 * T + (-1) * PowerSeries.X ^ 3 * T ^ 2) * hU
  have hnu0 : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16 : PowerSeries ℚ) = 16 := A243816Aux.cnum 16
    simp [kc] at h'
  have hnu : (16 * PowerSeries.X ^ 6 : PowerSeries ℚ) ≠ 0 := by
    have e : (16 * PowerSeries.X ^ 6 : PowerSeries ℚ) = PowerSeries.X ^ 6 * (16 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 6 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((-1) + (1) * T + (-1) * PowerSeries.X + (1) * PowerSeries.X * U) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 3) * (((-1) + (1) * T + (-1) * PowerSeries.X + (1) * PowerSeries.X * U) ^ 4 * ((PowerSeries.X ^ 4 : PowerSeries ℚ) + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (-2 * PowerSeries.X + 5 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4)) = 0 := by
    linear_combination ((-1) * PowerSeries.X ^ 7 + (2) * PowerSeries.X ^ 7 * T + (-1) * PowerSeries.X ^ 7 * T ^ 2 + (-4) * PowerSeries.X ^ 8 + (2) * PowerSeries.X ^ 8 * U + (4) * PowerSeries.X ^ 8 * T + (-2) * PowerSeries.X ^ 8 * T * U + (-2) * PowerSeries.X ^ 9 + (2) * PowerSeries.X ^ 9 * U) * hT +
      ((1) * PowerSeries.X ^ 7 + (-2) * PowerSeries.X ^ 7 * T + (1) * PowerSeries.X ^ 7 * T ^ 2 + (2) * PowerSeries.X ^ 8 + (-1) * PowerSeries.X ^ 8 * U + (-1) * PowerSeries.X ^ 8 * T + (1) * PowerSeries.X ^ 8 * T * U + (-1) * PowerSeries.X ^ 8 * T ^ 2 + (2) * PowerSeries.X ^ 9 + (-2) * PowerSeries.X ^ 9 * T + (7) * PowerSeries.X ^ 10 + (-4) * PowerSeries.X ^ 10 * U + (1) * PowerSeries.X ^ 10 * U ^ 2) * hU +
      ((-1) * PowerSeries.X ^ 3 * G ^ 2 + (3) * PowerSeries.X ^ 3 * G ^ 2 * T + (-3) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 + (-1) * PowerSeries.X ^ 3 * G ^ 3 + (3) * PowerSeries.X ^ 3 * G ^ 3 * T + (-3) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 2 + (1) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 + (1) * PowerSeries.X ^ 4 * G + (-3) * PowerSeries.X ^ 4 * G * T + (3) * PowerSeries.X ^ 4 * G * T ^ 2 + (-1) * PowerSeries.X ^ 4 * G * T ^ 3 + (3) * PowerSeries.X ^ 4 * G ^ 2 * U + (-3) * PowerSeries.X ^ 4 * G ^ 2 * T + (-6) * PowerSeries.X ^ 4 * G ^ 2 * T * U + (6) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (3) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 * U + (-3) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 + (-3) * PowerSeries.X ^ 4 * G ^ 3 + (3) * PowerSeries.X ^ 4 * G ^ 3 * U + (6) * PowerSeries.X ^ 4 * G ^ 3 * T + (-6) * PowerSeries.X ^ 4 * G ^ 3 * T * U + (-3) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 2 + (3) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 2 * U + (2) * PowerSeries.X ^ 5 * G + (-4) * PowerSeries.X ^ 5 * G * U + (-2) * PowerSeries.X ^ 5 * G * T + (8) * PowerSeries.X ^ 5 * G * T * U + (-2) * PowerSeries.X ^ 5 * G * T ^ 2 + (-4) * PowerSeries.X ^ 5 * G * T ^ 2 * U + (2) * PowerSeries.X ^ 5 * G * T ^ 3 + (7) * PowerSeries.X ^ 5 * G ^ 2 + (-4) * PowerSeries.X ^ 5 * G ^ 2 * U + (-3) * PowerSeries.X ^ 5 * G ^ 2 * U ^ 2 + (-17) * PowerSeries.X ^ 5 * G ^ 2 * T + (14) * PowerSeries.X ^ 5 * G ^ 2 * T * U + (3) * PowerSeries.X ^ 5 * G ^ 2 * T * U ^ 2 + (10) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (-10) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 * U + (-3) * PowerSeries.X ^ 5 * G ^ 3 + (6) * PowerSeries.X ^ 5 * G ^ 3 * U + (-3) * PowerSeries.X ^ 5 * G ^ 3 * U ^ 2 + (3) * PowerSeries.X ^ 5 * G ^ 3 * T + (-6) * PowerSeries.X ^ 5 * G ^ 3 * T * U + (3) * PowerSeries.X ^ 5 * G ^ 3 * T * U ^ 2 + (2) * PowerSeries.X ^ 6 + (-6) * PowerSeries.X ^ 6 * T + (6) * PowerSeries.X ^ 6 * T ^ 2 + (-2) * PowerSeries.X ^ 6 * T ^ 3 + (-3) * PowerSeries.X ^ 6 * G + (-2) * PowerSeries.X ^ 6 * G * U + (5) * PowerSeries.X ^ 6 * G * U ^ 2 + (11) * PowerSeries.X ^ 6 * G * T + (-6) * PowerSeries.X ^ 6 * G * T * U + (-5) * PowerSeries.X ^ 6 * G * T * U ^ 2 + (-8) * PowerSeries.X ^ 6 * G * T ^ 2 + (8) * PowerSeries.X ^ 6 * G * T ^ 2 * U + (10) * PowerSeries.X ^ 6 * G ^ 2 + (-19) * PowerSeries.X ^ 6 * G ^ 2 * U + (8) * PowerSeries.X ^ 6 * G ^ 2 * U ^ 2 + (1) * PowerSeries.X ^ 6 * G ^ 2 * U ^ 3 + (-11) * PowerSeries.X ^ 6 * G ^ 2 * T + (22) * PowerSeries.X ^ 6 * G ^ 2 * T * U + (-11) * PowerSeries.X ^ 6 * G ^ 2 * T * U ^ 2 + (-1) * PowerSeries.X ^ 6 * G ^ 3 + (3) * PowerSeries.X ^ 6 * G ^ 3 * U + (-3) * PowerSeries.X ^ 6 * G ^ 3 * U ^ 2 + (1) * PowerSeries.X ^ 6 * G ^ 3 * U ^ 3 + (5) * PowerSeries.X ^ 7 + (-4) * PowerSeries.X ^ 7 * U + (-1) * PowerSeries.X ^ 7 * U ^ 2 + (-11) * PowerSeries.X ^ 7 * T + (10) * PowerSeries.X ^ 7 * T * U + (1) * PowerSeries.X ^ 7 * T * U ^ 2 + (6) * PowerSeries.X ^ 7 * T ^ 2 + (-6) * PowerSeries.X ^ 7 * T ^ 2 * U + (-9) * PowerSeries.X ^ 7 * G + (16) * PowerSeries.X ^ 7 * G * U + (-5) * PowerSeries.X ^ 7 * G * U ^ 2 + (-2) * PowerSeries.X ^ 7 * G * U ^ 3 + (11) * PowerSeries.X ^ 7 * G * T + (-22) * PowerSeries.X ^ 7 * G * T * U + (11) * PowerSeries.X ^ 7 * G * T * U ^ 2 + (4) * PowerSeries.X ^ 7 * G ^ 2 + (-12) * PowerSeries.X ^ 7 * G ^ 2 * U + (12) * PowerSeries.X ^ 7 * G ^ 2 * U ^ 2 + (-4) * PowerSeries.X ^ 7 * G ^ 2 * U ^ 3 + (6) * PowerSeries.X ^ 8 + (-11) * PowerSeries.X ^ 8 * U + (4) * PowerSeries.X ^ 8 * U ^ 2 + (1) * PowerSeries.X ^ 8 * U ^ 3 + (-7) * PowerSeries.X ^ 8 * T + (14) * PowerSeries.X ^ 8 * T * U + (-7) * PowerSeries.X ^ 8 * T * U ^ 2 + (-5) * PowerSeries.X ^ 8 * G + (15) * PowerSeries.X ^ 8 * G * U + (-15) * PowerSeries.X ^ 8 * G * U ^ 2 + (5) * PowerSeries.X ^ 8 * G * U ^ 3 + (4) * PowerSeries.X ^ 9 + (-12) * PowerSeries.X ^ 9 * U + (12) * PowerSeries.X ^ 9 * U ^ 2 + (-4) * PowerSeries.X ^ 9 * U ^ 3) * hG
  have hLne : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 3) ≠ 0 := mul_ne_zero one_ne_zero (pow_ne_zero 3 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X ^ 4 : PowerSeries ℚ) + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (-2 * PowerSeries.X + 5 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (-1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243816Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243816Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A243816Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A243816Aux.rel G hP h0c m
        push_cast
        linear_combination r
