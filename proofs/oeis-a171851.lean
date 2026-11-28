import OMAStatements.S_oeis_a171851

-- Problem: A171851: The difference between the area under a peakless Motzkin path and the number of its U-steps, summed over all peakless Motzkin paths of length n (n>=0).
-- Upstream: formal-conjectures statements/oeis-a171851.lean:0 (declaration OMA.S_oeis_a171851.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A171851Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-2176 * X ^ 2 + 10968 * X ^ 3 - 13408 * X ^ 4 + 4528 * X ^ 5 - 23936 * X ^ 6 + 24904 * X ^ 7 - 4352 * X ^ 8 + 13232 * X ^ 9 - 11232 * X ^ 10 + 2264 * X ^ 11) * derivative ℚ (derivative ℚ G) + (6306 * X - 22885 * X ^ 2 + 24576 * X ^ 3 - 5762 * X ^ 4 - 50314 * X ^ 5 + 30569 * X ^ 6 - 20028 * X ^ 7 + 67814 * X ^ 8 - 60530 * X ^ 9 + 14099 * X ^ 10) * derivative ℚ G + (25668 - 104073 * X + 74306 * X ^ 2 + 12890 * X ^ 3 + 100740 * X ^ 4 - 82551 * X ^ 5 - 40104 * X ^ 6 + 63582 * X ^ 7 - 38066 * X ^ 8 + 9571 * X ^ 9) * G =
      31530 * X ^ 3 - 7800 * X ^ 4 + 3090 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d11 : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dnum 11
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d22 : derivative ℚ (22 : ℚ⟦X⟧) = 0 := dnum 22
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d42 : derivative ℚ (42 : ℚ⟦X⟧) = 0 := dnum 42
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d55 : derivative ℚ (55 : ℚ⟦X⟧) = 0 := dnum 55
  have d66 : derivative ℚ (66 : ℚ⟦X⟧) = 0 := dnum 66
  have d72 : derivative ℚ (72 : ℚ⟦X⟧) = 0 := dnum 72
  have hp0 : (2 * (X * X * X) - 1 * (X * X * X * X) + 2 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 + 9 * X - 10 * (X * X) + 6 * (X * X * X) - 18 * (X * X * X * X) + 11 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) + 2 * (X * X * X * X) + 11 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((2 * (X * X * X) - 1 * (X * X * X * X) + 2 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 + 9 * X - 10 * (X * X) + 6 * (X * X * X) - 18 * (X * X * X * X) + 11 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) + 2 * (X * X * X * X) + 11 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (6 * X ^ 2 - 4 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (9 - 20 * X + 18 * X ^ 2 - 72 * X ^ 3 + 55 * X ^ 4 - 48 * X ^ 5 + 42 * X ^ 6 - 32 * X ^ 7 + 9 * X ^ 8 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 + 8 * X ^ 3 + 66 * X ^ 5 + 16 * X ^ 7 - 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d9, d10, d11, d18]
    ring
  have hd1 : (6 * X ^ 2 - 4 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (9 - 20 * X + 18 * X ^ 2 - 72 * X ^ 3 + 55 * X ^ 4 - 48 * X ^ 5 + 42 * X ^ 6 - 32 * X ^ 7 + 9 * X ^ 8 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 + 8 * X ^ 3 + 66 * X ^ 5 + 16 * X ^ 7 - 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (6 * (X * X) - 4 * (X * X * X) + 10 * (X * X * X * X) : ℚ⟦X⟧) + (-2 + 9 * X - 10 * (X * X) + 6 * (X * X * X) - 18 * (X * X * X * X) + 11 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (9 - 20 * X + 18 * (X * X) - 72 * (X * X * X) + 55 * (X * X * X * X) - 48 * (X * X * X * X * X) + 42 * (X * X * X * X * X * X) - 32 * (X * X * X * X * X * X * X) + 9 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) + 22 * (X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * (X * X) + 8 * (X * X * X) + 66 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) - 36 * (X * X * X * X * X * X * X * X) + 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((6 * (X * X) - 4 * (X * X * X) + 10 * (X * X * X * X) : ℚ⟦X⟧) + (-2 + 9 * X - 10 * (X * X) + 6 * (X * X * X) - 18 * (X * X * X * X) + 11 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (9 - 20 * X + 18 * (X * X) - 72 * (X * X * X) + 55 * (X * X * X * X) - 48 * (X * X * X * X * X) + 42 * (X * X * X * X * X * X) - 32 * (X * X * X * X * X * X * X) + 9 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) + 22 * (X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * (X * X) + 8 * (X * X * X) + 66 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) - 36 * (X * X * X * X * X * X * X * X) + 10 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (12 * X - 12 * X ^ 2 + 40 * X ^ 3 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (18 - 40 * X + 36 * X ^ 2 - 144 * X ^ 3 + 110 * X ^ 4 - 96 * X ^ 5 + 84 * X ^ 6 - 64 * X ^ 7 + 18 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-20 + 36 * X - 216 * X ^ 2 + 220 * X ^ 3 - 240 * X ^ 4 + 252 * X ^ 5 - 224 * X ^ 6 + 72 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 + 32 * X ^ 3 + 264 * X ^ 5 + 64 * X ^ 7 - 144 * X ^ 8 + 40 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 24 * X + 24 * X ^ 2 + 330 * X ^ 4 + 112 * X ^ 6 - 288 * X ^ 7 + 90 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d9, d10, d11, d12, d16, d18, d20, d22, d32, d36, d42, d48, d55, d66, d72]
    ring
  have hd2 : (12 * X - 12 * X ^ 2 + 40 * X ^ 3 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (18 - 40 * X + 36 * X ^ 2 - 144 * X ^ 3 + 110 * X ^ 4 - 96 * X ^ 5 + 84 * X ^ 6 - 64 * X ^ 7 + 18 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-20 + 36 * X - 216 * X ^ 2 + 220 * X ^ 3 - 240 * X ^ 4 + 252 * X ^ 5 - 224 * X ^ 6 + 72 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 + 32 * X ^ 3 + 264 * X ^ 5 + 64 * X ^ 7 - 144 * X ^ 8 + 40 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 - 24 * X + 24 * X ^ 2 + 330 * X ^ 4 + 112 * X ^ 6 - 288 * X ^ 7 + 90 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G) ^ 3 * ((-2176 * X ^ 2 + 10968 * X ^ 3 - 13408 * X ^ 4 + 4528 * X ^ 5 - 23936 * X ^ 6 + 24904 * X ^ 7 - 4352 * X ^ 8 + 13232 * X ^ 9 - 11232 * X ^ 10 + 2264 * X ^ 11) * derivative ℚ (derivative ℚ G) + (6306 * X - 22885 * X ^ 2 + 24576 * X ^ 3 - 5762 * X ^ 4 - 50314 * X ^ 5 + 30569 * X ^ 6 - 20028 * X ^ 7 + 67814 * X ^ 8 - 60530 * X ^ 9 + 14099 * X ^ 10) * derivative ℚ G + (25668 - 104073 * X + 74306 * X ^ 2 + 12890 * X ^ 3 + 100740 * X ^ 4 - 82551 * X ^ 5 - 40104 * X ^ 6 + 63582 * X ^ 7 - 38066 * X ^ 8 + 9571 * X ^ 9) * G - (31530 * X ^ 3 - 7800 * X ^ 4 + 3090 * X ^ 5)) = 0 := by
    linear_combination ((102672 - 1226832 * X + 5709252 * X ^ 2 - 12955008 * X ^ 3 + 15896904 * X ^ 4 - 16649236 * X ^ 5 + 19798188 * X ^ 6 + 6104972 * X ^ 7 - 61872352 * X ^ 8 + 113529708 * X ^ 9 - 214107176 * X ^ 10 + 332082944 * X ^ 11 - 417818856 * X ^ 12 + 528113100 * X ^ 13 - 575798276 * X ^ 14 + 590489332 * X ^ 15 - 568866048 * X ^ 16 + 498351572 * X ^ 17 - 409822568 * X ^ 18 + 310394512 * X ^ 19 - 215759064 * X ^ 20 + 138006356 * X ^ 21 - 77777812 * X ^ 22 + 39151388 * X ^ 23 - 17271008 * X ^ 24 + 5613636 * X ^ 25 - 1070972 * X ^ 26 + 86440 * X ^ 27 : ℚ⟦X⟧) + (-240160 * X ^ 2 + 2648336 * X ^ 3 - 10770656 * X ^ 4 + 18799808 * X ^ 5 - 13409264 * X ^ 6 + 15367152 * X ^ 7 - 25955152 * X ^ 8 - 39271360 * X ^ 9 + 110595984 * X ^ 10 - 122777760 * X ^ 11 + 280093344 * X ^ 12 - 385577536 * X ^ 13 + 399053392 * X ^ 14 - 544319440 * X ^ 15 + 509137040 * X ^ 16 - 500129216 * X ^ 17 + 462747056 * X ^ 18 - 366302880 * X ^ 19 + 277828000 * X ^ 20 - 201217856 * X ^ 21 + 126176304 * X ^ 22 - 68966928 * X ^ 23 + 36053424 * X ^ 24 - 16174784 * X ^ 25 + 4894608 * X ^ 26 - 817648 * X ^ 27 + 55968 * X ^ 28 : ℚ⟦X⟧) * G + (120080 * X ^ 4 - 1264128 * X ^ 5 + 4633184 * X ^ 6 - 6059344 * X ^ 7 + 1089712 * X ^ 8 - 6730192 * X ^ 9 + 13555776 * X ^ 10 + 29185072 * X ^ 11 - 40282912 * X ^ 12 + 16426816 * X ^ 13 - 125613536 * X ^ 14 + 128432688 * X ^ 15 - 96922384 * X ^ 16 + 224179344 * X ^ 17 - 141138752 * X ^ 18 + 165234832 * X ^ 19 - 169146784 * X ^ 20 + 104680192 * X ^ 21 - 96613152 * X ^ 22 + 72359696 * X ^ 23 - 36771536 * X ^ 24 + 22568432 * X ^ 25 - 13351936 * X ^ 26 + 4670736 * X ^ 27 - 817648 * X ^ 28 + 55968 * X ^ 29 : ℚ⟦X⟧) * G ^ 2) * hP +
      ((25224 * X - 396892 * X ^ 2 + 2606630 * X ^ 3 - 9431949 * X ^ 4 + 21971372 * X ^ 5 - 41045134 * X ^ 6 + 75569174 * X ^ 7 - 126741681 * X ^ 8 + 177344748 * X ^ 9 - 239738902 * X ^ 10 + 318197148 * X ^ 11 - 364429586 * X ^ 12 + 399108444 * X ^ 13 - 431379718 * X ^ 14 + 414782198 * X ^ 15 - 378774105 * X ^ 16 + 333543156 * X ^ 17 - 270281642 * X ^ 18 + 202946684 * X ^ 19 - 143815250 * X ^ 20 + 94479540 * X ^ 21 - 56211234 * X ^ 22 + 29890550 * X ^ 23 - 14358001 * X ^ 24 + 5968828 * X ^ 25 - 1833174 * X ^ 26 + 336758 * X ^ 27 - 26653 * X ^ 28 : ℚ⟦X⟧) + (-8704 * X ^ 4 + 117856 * X ^ 5 - 644144 * X ^ 6 + 1849312 * X ^ 7 - 3359968 * X ^ 8 + 5769376 * X ^ 9 - 11224560 * X ^ 10 + 16810688 * X ^ 11 - 19952544 * X ^ 12 + 29146656 * X ^ 13 - 37747552 * X ^ 14 + 35748640 * X ^ 15 - 41687136 * X ^ 16 + 45458528 * X ^ 17 - 37112432 * X ^ 18 + 34471360 * X ^ 19 - 30930784 * X ^ 20 + 22481248 * X ^ 21 - 15938144 * X ^ 22 + 11587296 * X ^ 23 - 7183520 * X ^ 24 + 3748832 * X ^ 25 - 1951984 * X ^ 26 + 940672 * X ^ 27 - 314848 * X ^ 28 + 58688 * X ^ 29 - 4528 * X ^ 30 : ℚ⟦X⟧) * (derivative ℚ G) + (-85264 * X ^ 3 + 1192112 * X ^ 4 - 6765652 * X ^ 5 + 20301368 * X ^ 6 - 38412280 * X ^ 7 + 66193216 * X ^ 8 - 128704340 * X ^ 9 + 199653504 * X ^ 10 - 241926536 * X ^ 11 + 348160680 * X ^ 12 - 464543032 * X ^ 13 + 452236520 * X ^ 14 - 518419128 * X ^ 15 + 582433232 * X ^ 16 - 485359220 * X ^ 17 + 450116960 * X ^ 18 - 411478648 * X ^ 19 + 306736664 * X ^ 20 - 218335256 * X ^ 21 + 161424920 * X ^ 22 - 102989800 * X ^ 23 + 54399664 * X ^ 24 - 28780852 * X ^ 25 + 14393008 * X ^ 26 - 4991400 * X ^ 27 + 954328 * X ^ 28 - 74916 * X ^ 29 : ℚ⟦X⟧) * G + (8704 * X ^ 6 - 113504 * X ^ 7 + 578688 * X ^ 8 - 1463872 * X ^ 9 + 2241536 * X ^ 10 - 3992544 * X ^ 11 + 8691968 * X ^ 12 - 11221696 * X ^ 13 + 11539584 * X ^ 14 - 22237632 * X ^ 15 + 26279808 * X ^ 16 - 17998656 * X ^ 17 + 31899392 * X ^ 18 - 32551648 * X ^ 19 + 17912064 * X ^ 20 - 26041152 * X ^ 21 + 22624128 * X ^ 22 - 11583936 * X ^ 23 + 11191424 * X ^ 24 - 8819392 * X ^ 25 + 4052736 * X ^ 26 - 2251744 * X ^ 27 + 1484288 * X ^ 28 - 593472 * X ^ 29 + 117376 * X ^ 30 - 9056 * X ^ 31 : ℚ⟦X⟧) * G * (derivative ℚ G) + (51336 * X ^ 5 - 686068 * X ^ 6 + 3595520 * X ^ 7 - 9386776 * X ^ 8 + 14770216 * X ^ 9 - 26221796 * X ^ 10 + 57846576 * X ^ 11 - 77560680 * X ^ 12 + 79966432 * X ^ 13 - 152951272 * X ^ 14 + 189880992 * X ^ 15 - 130779832 * X ^ 16 + 226404040 * X ^ 17 - 246893124 * X ^ 18 + 132905104 * X ^ 19 - 194266968 * X ^ 20 + 176585536 * X ^ 21 - 89848360 * X ^ 22 + 87007072 * X ^ 23 - 70809992 * X ^ 24 + 32893064 * X ^ 25 - 18231588 * X ^ 26 + 12278000 * X ^ 27 - 5024696 * X ^ 28 + 1013016 * X ^ 29 - 79444 * X ^ 30 : ℚ⟦X⟧) * G ^ 2) * hd1 +
      ((-8704 * X ^ 2 + 122208 * X ^ 3 - 711776 * X ^ 4 + 2271832 * X ^ 5 - 4727872 * X ^ 6 + 8377360 * X ^ 7 - 15202720 * X ^ 8 + 24097144 * X ^ 9 - 31668352 * X ^ 10 + 42102544 * X ^ 11 - 53958272 * X ^ 12 + 58368112 * X ^ 13 - 62232768 * X ^ 14 + 65052752 * X ^ 15 - 59822496 * X ^ 16 + 52438200 * X ^ 17 - 44578688 * X ^ 18 + 34833392 * X ^ 19 - 24833792 * X ^ 20 + 16907888 * X ^ 21 - 10750784 * X ^ 22 + 6054128 * X ^ 23 - 3060256 * X ^ 24 + 1425272 * X ^ 25 - 569600 * X ^ 26 + 166480 * X ^ 27 - 29344 * X ^ 28 + 2264 * X ^ 29 : ℚ⟦X⟧) + (17408 * X ^ 4 - 235712 * X ^ 5 + 1288288 * X ^ 6 - 3698624 * X ^ 7 + 6719936 * X ^ 8 - 11538752 * X ^ 9 + 22449120 * X ^ 10 - 33621376 * X ^ 11 + 39905088 * X ^ 12 - 58293312 * X ^ 13 + 75495104 * X ^ 14 - 71497280 * X ^ 15 + 83374272 * X ^ 16 - 90917056 * X ^ 17 + 74224864 * X ^ 18 - 68942720 * X ^ 19 + 61861568 * X ^ 20 - 44962496 * X ^ 21 + 31876288 * X ^ 22 - 23174592 * X ^ 23 + 14367040 * X ^ 24 - 7497664 * X ^ 25 + 3903968 * X ^ 26 - 1881344 * X ^ 27 + 629696 * X ^ 28 - 117376 * X ^ 29 + 9056 * X ^ 30 : ℚ⟦X⟧) * G + (-8704 * X ^ 6 + 113504 * X ^ 7 - 578688 * X ^ 8 + 1463872 * X ^ 9 - 2241536 * X ^ 10 + 3992544 * X ^ 11 - 8691968 * X ^ 12 + 11221696 * X ^ 13 - 11539584 * X ^ 14 + 22237632 * X ^ 15 - 26279808 * X ^ 16 + 17998656 * X ^ 17 - 31899392 * X ^ 18 + 32551648 * X ^ 19 - 17912064 * X ^ 20 + 26041152 * X ^ 21 - 22624128 * X ^ 22 + 11583936 * X ^ 23 - 11191424 * X ^ 24 + 8819392 * X ^ 25 - 4052736 * X ^ 26 + 2251744 * X ^ 27 - 1484288 * X ^ 28 + 593472 * X ^ 29 - 117376 * X ^ 30 + 9056 * X ^ 31 : ℚ⟦X⟧) * G ^ 2) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-2176) + derivative ℚ (derivative ℚ G) * X * X * X * C 10968 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-13408) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 4528 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-23936) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 24904 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-4352) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * C 13232 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * C (-11232) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * X * X * C 2264 +
      derivative ℚ G * X * C 6306 + derivative ℚ G * X * X * C (-22885) +
      derivative ℚ G * X * X * X * C 24576 + derivative ℚ G * X * X * X * X * C (-5762) +
      derivative ℚ G * X * X * X * X * X * C (-50314) + derivative ℚ G * X * X * X * X * X * X * C 30569 +
      derivative ℚ G * X * X * X * X * X * X * X * C (-20028) + derivative ℚ G * X * X * X * X * X * X * X * X * C 67814 +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C (-60530) + derivative ℚ G * X * X * X * X * X * X * X * X * X * X * C 14099 +
      G * C 25668 + G * X * C (-104073) +
      G * X * X * C 74306 + G * X * X * X * C 12890 +
      G * X * X * X * X * C 100740 + G * X * X * X * X * X * C (-82551) +
      G * X * X * X * X * X * X * C (-40104) + G * X * X * X * X * X * X * X * C 63582 +
      G * X * X * X * X * X * X * X * X * C (-38066) + G * X * X * X * X * X * X * X * X * X * C 9571 =
      C 31530 * X * X * X + C (-7800) * X * X * X * X +
      C 3090 * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-2176) * ((m : ℚ) + 11) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 10968 * ((m : ℚ) + 10) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-13408) * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4528 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-23936) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 24904 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4352) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 13232 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-11232) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 2264 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      6306 * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22885) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      24576 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5762) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-50314) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 30569 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-20028) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 67814 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-60530) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 14099 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      25668 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-104073) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      74306 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 12890 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      100740 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-82551) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-40104) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 63582 * coeff (m + 1 + 1 + 1 + 1) G +
      (-38066) * coeff (m + 1 + 1 + 1) G + 9571 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-156672) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 614208 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-563136) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 135840 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-478720) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 298848 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-26112) * coeff (0 + 1 + 1 + 1) G + 26464 * coeff (0 + 1 + 1) G +
      56754 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-183080) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      172032 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-34572) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-251570) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 122276 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-60084) * coeff (0 + 1 + 1 + 1) G + 135628 * coeff (0 + 1 + 1) G +
      (-60530) * coeff (0 + 1) G + 25668 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-104073) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 74306 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      12890 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 100740 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-82551) * coeff (0 + 1 + 1 + 1 + 1) G + (-40104) * coeff (0 + 1 + 1 + 1) G +
      63582 * coeff (0 + 1 + 1) G + (-38066) * coeff (0 + 1) G +
      9571 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-2 + 9 * X - 10 * X ^ 2 + 6 * X ^ 3 - 18 * X ^ 4 + 11 * X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-195840) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 789696 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-750848) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 190176 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-718080) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 498080 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-52224) * coeff (0 + 1 + 1 + 1 + 1) G + 79392 * coeff (0 + 1 + 1 + 1) G +
      (-22464) * coeff (0 + 1 + 1) G + 63060 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-205965) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 196608 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-40334) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-301884) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      152845 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-80112) * coeff (0 + 1 + 1 + 1 + 1) G +
      203442 * coeff (0 + 1 + 1 + 1) G + (-121060) * coeff (0 + 1 + 1) G +
      14099 * coeff (0 + 1) G + 25668 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-104073) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 74306 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      12890 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 100740 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-82551) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-40104) * coeff (0 + 1 + 1 + 1 + 1) G +
      63582 * coeff (0 + 1 + 1 + 1) G + (-38066) * coeff (0 + 1 + 1) G +
      9571 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A171851Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a171851.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 9, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m + 1 := rfl
  have e9 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 9 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A171851Aux.cnum 2
  have kn3 : PowerSeries.constantCoeff (3 : PowerSeries ℚ) = 3 := A171851Aux.cnum 3
  have kn4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 := A171851Aux.cnum 4
  have hN1 : ((1) + (-2) * PowerSeries.X + (3) * PowerSeries.X ^ 2 + (-4) * PowerSeries.X ^ 2 * T + (-2) * PowerSeries.X ^ 3 + (4) * PowerSeries.X ^ 3 * T + (1) * PowerSeries.X ^ 4 + (-4) * PowerSeries.X ^ 4 * T + (4) * PowerSeries.X ^ 4 * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn2, kn3, kn4] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 10) * (((1) + (-2) * PowerSeries.X + (3) * PowerSeries.X ^ 2 + (-4) * PowerSeries.X ^ 2 * T + (-2) * PowerSeries.X ^ 3 + (4) * PowerSeries.X ^ 3 * T + (1) * PowerSeries.X ^ 4 + (-4) * PowerSeries.X ^ 4 * T + (4) * PowerSeries.X ^ 4 * T ^ 2) ^ 2 * ((2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5 : PowerSeries ℚ) + (-2 + 9 * PowerSeries.X - 10 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 - 18 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 5 - 8 * PowerSeries.X ^ 6 + 6 * PowerSeries.X ^ 7 - 4 * PowerSeries.X ^ 8 + PowerSeries.X ^ 9 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((2) * PowerSeries.X ^ 13 + (2) * PowerSeries.X ^ 13 * T + (-9) * PowerSeries.X ^ 14 + (-11) * PowerSeries.X ^ 14 * T + (4) * PowerSeries.X ^ 14 * T ^ 2 + (26) * PowerSeries.X ^ 15 + (21) * PowerSeries.X ^ 15 * T + (-28) * PowerSeries.X ^ 15 * T ^ 2 + (-50) * PowerSeries.X ^ 16 + (-29) * PowerSeries.X ^ 16 * T + (73) * PowerSeries.X ^ 16 * T ^ 2 + (-12) * PowerSeries.X ^ 16 * T ^ 3 + (74) * PowerSeries.X ^ 17 + (14) * PowerSeries.X ^ 17 * T + (-108) * PowerSeries.X ^ 17 * T ^ 2 + (56) * PowerSeries.X ^ 17 * T ^ 3 + (-83) * PowerSeries.X ^ 18 + (1) * PowerSeries.X ^ 18 * T + (142) * PowerSeries.X ^ 18 * T ^ 2 + (-76) * PowerSeries.X ^ 18 * T ^ 3 + (4) * PowerSeries.X ^ 18 * T ^ 4 + (74) * PowerSeries.X ^ 19 + (-17) * PowerSeries.X ^ 19 * T + (-132) * PowerSeries.X ^ 19 * T ^ 2 + (64) * PowerSeries.X ^ 19 * T ^ 3 + (-16) * PowerSeries.X ^ 19 * T ^ 4 + (-50) * PowerSeries.X ^ 20 + (1) * PowerSeries.X ^ 20 * T + (147) * PowerSeries.X ^ 20 * T ^ 2 + (-108) * PowerSeries.X ^ 20 * T ^ 3 + (8) * PowerSeries.X ^ 20 * T ^ 4 + (26) * PowerSeries.X ^ 21 + (14) * PowerSeries.X ^ 21 * T + (-112) * PowerSeries.X ^ 21 * T ^ 2 + (88) * PowerSeries.X ^ 21 * T ^ 3 + (-9) * PowerSeries.X ^ 22 + (-29) * PowerSeries.X ^ 22 * T + (102) * PowerSeries.X ^ 22 * T ^ 2 + (-100) * PowerSeries.X ^ 22 * T ^ 3 + (44) * PowerSeries.X ^ 22 * T ^ 4 + (2) * PowerSeries.X ^ 23 + (21) * PowerSeries.X ^ 23 * T + (-56) * PowerSeries.X ^ 23 * T ^ 2 + (32) * PowerSeries.X ^ 23 * T ^ 3 + (-11) * PowerSeries.X ^ 24 * T + (33) * PowerSeries.X ^ 24 * T ^ 2 + (-36) * PowerSeries.X ^ 24 * T ^ 3 + (8) * PowerSeries.X ^ 24 * T ^ 4 + (2) * PowerSeries.X ^ 25 * T + (-8) * PowerSeries.X ^ 25 * T ^ 2 + (24) * PowerSeries.X ^ 25 * T ^ 3 + (-16) * PowerSeries.X ^ 25 * T ^ 4 + (-4) * PowerSeries.X ^ 26 * T ^ 3 + (4) * PowerSeries.X ^ 26 * T ^ 4) * hT +
      ((2) * PowerSeries.X ^ 10 + (-13) * PowerSeries.X ^ 11 + (34) * PowerSeries.X ^ 12 + (-8) * PowerSeries.X ^ 12 * T + (-1) * PowerSeries.X ^ 12 * G + (-57) * PowerSeries.X ^ 13 + (44) * PowerSeries.X ^ 13 * T + (6) * PowerSeries.X ^ 13 * G + (80) * PowerSeries.X ^ 14 + (-84) * PowerSeries.X ^ 14 * T + (8) * PowerSeries.X ^ 14 * T ^ 2 + (-13) * PowerSeries.X ^ 14 * G + (4) * PowerSeries.X ^ 14 * G * T + (-94) * PowerSeries.X ^ 15 + (100) * PowerSeries.X ^ 15 * T + (-37) * PowerSeries.X ^ 15 * T ^ 2 + (18) * PowerSeries.X ^ 15 * G + (-20) * PowerSeries.X ^ 15 * G * T + (106) * PowerSeries.X ^ 16 + (-136) * PowerSeries.X ^ 16 * T + (46) * PowerSeries.X ^ 16 * T ^ 2 + (-2) * PowerSeries.X ^ 16 * T ^ 3 + (-26) * PowerSeries.X ^ 16 * G + (28) * PowerSeries.X ^ 16 * G * T + (-4) * PowerSeries.X ^ 16 * G * T ^ 2 + (-97) * PowerSeries.X ^ 17 + (140) * PowerSeries.X ^ 17 * T + (-34) * PowerSeries.X ^ 17 * T ^ 2 + (8) * PowerSeries.X ^ 17 * T ^ 3 + (30) * PowerSeries.X ^ 17 * G + (-24) * PowerSeries.X ^ 17 * G * T + (16) * PowerSeries.X ^ 17 * G * T ^ 2 + (80) * PowerSeries.X ^ 18 + (-148) * PowerSeries.X ^ 18 * T + (76) * PowerSeries.X ^ 18 * T ^ 2 + (-4) * PowerSeries.X ^ 18 * T ^ 3 + (-37) * PowerSeries.X ^ 18 * G + (52) * PowerSeries.X ^ 18 * G * T + (-8) * PowerSeries.X ^ 18 * G * T ^ 2 + (-54) * PowerSeries.X ^ 19 + (100) * PowerSeries.X ^ 19 * T + (-55) * PowerSeries.X ^ 19 * T ^ 2 + (30) * PowerSeries.X ^ 19 * G + (-44) * PowerSeries.X ^ 19 * G * T + (34) * PowerSeries.X ^ 20 + (-72) * PowerSeries.X ^ 20 * T + (54) * PowerSeries.X ^ 20 * T ^ 2 + (-22) * PowerSeries.X ^ 20 * T ^ 3 + (-26) * PowerSeries.X ^ 20 * G + (52) * PowerSeries.X ^ 20 * G * T + (-44) * PowerSeries.X ^ 20 * G * T ^ 2 + (-17) * PowerSeries.X ^ 21 + (44) * PowerSeries.X ^ 21 * T + (-26) * PowerSeries.X ^ 21 * T ^ 2 + (18) * PowerSeries.X ^ 21 * G + (-24) * PowerSeries.X ^ 21 * G * T + (6) * PowerSeries.X ^ 22 + (-20) * PowerSeries.X ^ 22 * T + (24) * PowerSeries.X ^ 22 * T ^ 2 + (-4) * PowerSeries.X ^ 22 * T ^ 3 + (-13) * PowerSeries.X ^ 22 * G + (28) * PowerSeries.X ^ 22 * G * T + (-8) * PowerSeries.X ^ 22 * G * T ^ 2 + (-1) * PowerSeries.X ^ 23 + (4) * PowerSeries.X ^ 23 * T + (-13) * PowerSeries.X ^ 23 * T ^ 2 + (8) * PowerSeries.X ^ 23 * T ^ 3 + (6) * PowerSeries.X ^ 23 * G + (-20) * PowerSeries.X ^ 23 * G * T + (16) * PowerSeries.X ^ 23 * G * T ^ 2 + (2) * PowerSeries.X ^ 24 * T ^ 2 + (-2) * PowerSeries.X ^ 24 * T ^ 3 + (-1) * PowerSeries.X ^ 24 * G + (4) * PowerSeries.X ^ 24 * G * T + (-4) * PowerSeries.X ^ 24 * G * T ^ 2) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 10) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 10 PowerSeries.X_ne_zero)
  have hP : (2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5 : PowerSeries ℚ) + (-2 + 9 * PowerSeries.X - 10 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 - 18 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 5 - 8 * PowerSeries.X ^ 6 + 6 * PowerSeries.X ^ 7 - 4 * PowerSeries.X ^ 8 + PowerSeries.X ^ 9 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A171851Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A171851Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A171851Aux.rel G hP h0c m
      push_cast
      linear_combination r
