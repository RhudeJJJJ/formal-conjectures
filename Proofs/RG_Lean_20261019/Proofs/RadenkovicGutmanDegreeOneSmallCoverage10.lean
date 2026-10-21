/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block000
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block001
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block002
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block003
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block004
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block005
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block006
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block007
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block008
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block009
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block010
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block011
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block012
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block013
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block014
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block015
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block016
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block017
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block018
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block019
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block020
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block021
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block022
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block023
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block024
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block025
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block026
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block027
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block028
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block029
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block030
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block031
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block032
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block033
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block034
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block035
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block036
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block037
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block038
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block039
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block040
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block041
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block042
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block043
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block044
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block045
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block046
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block047
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block048
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block049
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block050
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block051
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block052
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block053
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block054
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block055
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block056
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage10Block057
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered10 : decide (∀ i : Fin (RootedCatalogueData.catalogue 10).length,
    ∀ p q : Fin 11, eligible 10 i.val p.val q.val=true →
      (⟨10,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 1842 at hi
  by_cases h0 : i.val < 32
  · exact range_sound 10 0 32 checked10b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 64
    · exact range_sound 10 32 32 checked10b001 i.val p q (by omega) (by omega) he
    ·
      by_cases h2 : i.val < 96
      · exact range_sound 10 64 32 checked10b002 i.val p q (by omega) (by omega) he
      ·
        by_cases h3 : i.val < 128
        · exact range_sound 10 96 32 checked10b003 i.val p q (by omega) (by omega) he
        ·
          by_cases h4 : i.val < 160
          · exact range_sound 10 128 32 checked10b004 i.val p q (by omega) (by omega) he
          ·
            by_cases h5 : i.val < 192
            · exact range_sound 10 160 32 checked10b005 i.val p q (by omega) (by omega) he
            ·
              by_cases h6 : i.val < 224
              · exact range_sound 10 192 32 checked10b006 i.val p q (by omega) (by omega) he
              ·
                by_cases h7 : i.val < 256
                · exact range_sound 10 224 32 checked10b007 i.val p q (by omega) (by omega) he
                ·
                  by_cases h8 : i.val < 288
                  · exact range_sound 10 256 32 checked10b008 i.val p q (by omega) (by omega) he
                  ·
                    by_cases h9 : i.val < 320
                    · exact range_sound 10 288 32 checked10b009 i.val p q (by omega) (by omega) he
                    ·
                      by_cases h10 : i.val < 352
                      · exact range_sound 10 320 32 checked10b010 i.val p q (by omega) (by omega) he
                      ·
                        by_cases h11 : i.val < 384
                        · exact range_sound 10 352 32 checked10b011 i.val p q (by omega) (by omega) he
                        ·
                          by_cases h12 : i.val < 416
                          · exact range_sound 10 384 32 checked10b012 i.val p q (by omega) (by omega) he
                          ·
                            by_cases h13 : i.val < 448
                            · exact range_sound 10 416 32 checked10b013 i.val p q (by omega) (by omega) he
                            ·
                              by_cases h14 : i.val < 480
                              · exact range_sound 10 448 32 checked10b014 i.val p q (by omega) (by omega) he
                              ·
                                by_cases h15 : i.val < 512
                                · exact range_sound 10 480 32 checked10b015 i.val p q (by omega) (by omega) he
                                ·
                                  by_cases h16 : i.val < 544
                                  · exact range_sound 10 512 32 checked10b016 i.val p q (by omega) (by omega) he
                                  ·
                                    by_cases h17 : i.val < 576
                                    · exact range_sound 10 544 32 checked10b017 i.val p q (by omega) (by omega) he
                                    ·
                                      by_cases h18 : i.val < 608
                                      · exact range_sound 10 576 32 checked10b018 i.val p q (by omega) (by omega) he
                                      ·
                                        by_cases h19 : i.val < 640
                                        · exact range_sound 10 608 32 checked10b019 i.val p q (by omega) (by omega) he
                                        ·
                                          by_cases h20 : i.val < 672
                                          · exact range_sound 10 640 32 checked10b020 i.val p q (by omega) (by omega) he
                                          ·
                                            by_cases h21 : i.val < 704
                                            · exact range_sound 10 672 32 checked10b021 i.val p q (by omega) (by omega) he
                                            ·
                                              by_cases h22 : i.val < 736
                                              · exact range_sound 10 704 32 checked10b022 i.val p q (by omega) (by omega) he
                                              ·
                                                by_cases h23 : i.val < 768
                                                · exact range_sound 10 736 32 checked10b023 i.val p q (by omega) (by omega) he
                                                ·
                                                  by_cases h24 : i.val < 800
                                                  · exact range_sound 10 768 32 checked10b024 i.val p q (by omega) (by omega) he
                                                  ·
                                                    by_cases h25 : i.val < 832
                                                    · exact range_sound 10 800 32 checked10b025 i.val p q (by omega) (by omega) he
                                                    ·
                                                      by_cases h26 : i.val < 864
                                                      · exact range_sound 10 832 32 checked10b026 i.val p q (by omega) (by omega) he
                                                      ·
                                                        by_cases h27 : i.val < 896
                                                        · exact range_sound 10 864 32 checked10b027 i.val p q (by omega) (by omega) he
                                                        ·
                                                          by_cases h28 : i.val < 928
                                                          · exact range_sound 10 896 32 checked10b028 i.val p q (by omega) (by omega) he
                                                          ·
                                                            by_cases h29 : i.val < 960
                                                            · exact range_sound 10 928 32 checked10b029 i.val p q (by omega) (by omega) he
                                                            ·
                                                              by_cases h30 : i.val < 992
                                                              · exact range_sound 10 960 32 checked10b030 i.val p q (by omega) (by omega) he
                                                              ·
                                                                by_cases h31 : i.val < 1024
                                                                · exact range_sound 10 992 32 checked10b031 i.val p q (by omega) (by omega) he
                                                                ·
                                                                  by_cases h32 : i.val < 1056
                                                                  · exact range_sound 10 1024 32 checked10b032 i.val p q (by omega) (by omega) he
                                                                  ·
                                                                    by_cases h33 : i.val < 1088
                                                                    · exact range_sound 10 1056 32 checked10b033 i.val p q (by omega) (by omega) he
                                                                    ·
                                                                      by_cases h34 : i.val < 1120
                                                                      · exact range_sound 10 1088 32 checked10b034 i.val p q (by omega) (by omega) he
                                                                      ·
                                                                        by_cases h35 : i.val < 1152
                                                                        · exact range_sound 10 1120 32 checked10b035 i.val p q (by omega) (by omega) he
                                                                        ·
                                                                          by_cases h36 : i.val < 1184
                                                                          · exact range_sound 10 1152 32 checked10b036 i.val p q (by omega) (by omega) he
                                                                          ·
                                                                            by_cases h37 : i.val < 1216
                                                                            · exact range_sound 10 1184 32 checked10b037 i.val p q (by omega) (by omega) he
                                                                            ·
                                                                              by_cases h38 : i.val < 1248
                                                                              · exact range_sound 10 1216 32 checked10b038 i.val p q (by omega) (by omega) he
                                                                              ·
                                                                                by_cases h39 : i.val < 1280
                                                                                · exact range_sound 10 1248 32 checked10b039 i.val p q (by omega) (by omega) he
                                                                                ·
                                                                                  by_cases h40 : i.val < 1312
                                                                                  · exact range_sound 10 1280 32 checked10b040 i.val p q (by omega) (by omega) he
                                                                                  ·
                                                                                    by_cases h41 : i.val < 1344
                                                                                    · exact range_sound 10 1312 32 checked10b041 i.val p q (by omega) (by omega) he
                                                                                    ·
                                                                                      by_cases h42 : i.val < 1376
                                                                                      · exact range_sound 10 1344 32 checked10b042 i.val p q (by omega) (by omega) he
                                                                                      ·
                                                                                        by_cases h43 : i.val < 1408
                                                                                        · exact range_sound 10 1376 32 checked10b043 i.val p q (by omega) (by omega) he
                                                                                        ·
                                                                                          by_cases h44 : i.val < 1440
                                                                                          · exact range_sound 10 1408 32 checked10b044 i.val p q (by omega) (by omega) he
                                                                                          ·
                                                                                            by_cases h45 : i.val < 1472
                                                                                            · exact range_sound 10 1440 32 checked10b045 i.val p q (by omega) (by omega) he
                                                                                            ·
                                                                                              by_cases h46 : i.val < 1504
                                                                                              · exact range_sound 10 1472 32 checked10b046 i.val p q (by omega) (by omega) he
                                                                                              ·
                                                                                                by_cases h47 : i.val < 1536
                                                                                                · exact range_sound 10 1504 32 checked10b047 i.val p q (by omega) (by omega) he
                                                                                                ·
                                                                                                  by_cases h48 : i.val < 1568
                                                                                                  · exact range_sound 10 1536 32 checked10b048 i.val p q (by omega) (by omega) he
                                                                                                  ·
                                                                                                    by_cases h49 : i.val < 1600
                                                                                                    · exact range_sound 10 1568 32 checked10b049 i.val p q (by omega) (by omega) he
                                                                                                    ·
                                                                                                      by_cases h50 : i.val < 1632
                                                                                                      · exact range_sound 10 1600 32 checked10b050 i.val p q (by omega) (by omega) he
                                                                                                      ·
                                                                                                        by_cases h51 : i.val < 1664
                                                                                                        · exact range_sound 10 1632 32 checked10b051 i.val p q (by omega) (by omega) he
                                                                                                        ·
                                                                                                          by_cases h52 : i.val < 1696
                                                                                                          · exact range_sound 10 1664 32 checked10b052 i.val p q (by omega) (by omega) he
                                                                                                          ·
                                                                                                            by_cases h53 : i.val < 1728
                                                                                                            · exact range_sound 10 1696 32 checked10b053 i.val p q (by omega) (by omega) he
                                                                                                            ·
                                                                                                              by_cases h54 : i.val < 1760
                                                                                                              · exact range_sound 10 1728 32 checked10b054 i.val p q (by omega) (by omega) he
                                                                                                              ·
                                                                                                                by_cases h55 : i.val < 1792
                                                                                                                · exact range_sound 10 1760 32 checked10b055 i.val p q (by omega) (by omega) he
                                                                                                                ·
                                                                                                                  by_cases h56 : i.val < 1824
                                                                                                                  · exact range_sound 10 1792 32 checked10b056 i.val p q (by omega) (by omega) he
                                                                                                                  ·
                                                                                                                    exact range_sound 10 1824 18 checked10b057 i.val p q (by omega) (by omega) he
#print axioms covered10
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
