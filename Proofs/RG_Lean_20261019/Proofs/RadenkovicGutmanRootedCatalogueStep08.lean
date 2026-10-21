/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block000
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block001
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block002
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block003
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block004
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block005
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block006
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block007
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block008
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block009
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block010
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block011
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block012
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block013
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block014
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block015
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block016
import Proofs.RadenkovicGutmanRootedCatalogueStep08Block017
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem step8 : ∀ i : Fin level8.length, ∀ v : Vertices 8,
    ∃ j : Fin level9.length,
      ∃ e : graph (n := 9) (level8.get i,v) ≃g graph (level9.get j),
        e (root 9)=root 9 := by
  intro i v
  have hi := i.isLt
  change i.val < 286 at hi
  by_cases h0 : i.val < 16
  · exact range_sound 8 level8 level9 0 16 (by decide) witnesses8b000 checked8b000
      ⟨i.val-0,by omega⟩ v i (by change 0+(i.val-0)=i.val; omega)
  ·
    by_cases h1 : i.val < 32
    · exact range_sound 8 level8 level9 16 16 (by decide) witnesses8b001 checked8b001
        ⟨i.val-16,by omega⟩ v i (by change 16+(i.val-16)=i.val; omega)
    ·
      by_cases h2 : i.val < 48
      · exact range_sound 8 level8 level9 32 16 (by decide) witnesses8b002 checked8b002
          ⟨i.val-32,by omega⟩ v i (by change 32+(i.val-32)=i.val; omega)
      ·
        by_cases h3 : i.val < 64
        · exact range_sound 8 level8 level9 48 16 (by decide) witnesses8b003 checked8b003
            ⟨i.val-48,by omega⟩ v i (by change 48+(i.val-48)=i.val; omega)
        ·
          by_cases h4 : i.val < 80
          · exact range_sound 8 level8 level9 64 16 (by decide) witnesses8b004 checked8b004
              ⟨i.val-64,by omega⟩ v i (by change 64+(i.val-64)=i.val; omega)
          ·
            by_cases h5 : i.val < 96
            · exact range_sound 8 level8 level9 80 16 (by decide) witnesses8b005 checked8b005
                ⟨i.val-80,by omega⟩ v i (by change 80+(i.val-80)=i.val; omega)
            ·
              by_cases h6 : i.val < 112
              · exact range_sound 8 level8 level9 96 16 (by decide) witnesses8b006 checked8b006
                  ⟨i.val-96,by omega⟩ v i (by change 96+(i.val-96)=i.val; omega)
              ·
                by_cases h7 : i.val < 128
                · exact range_sound 8 level8 level9 112 16 (by decide) witnesses8b007 checked8b007
                    ⟨i.val-112,by omega⟩ v i (by change 112+(i.val-112)=i.val; omega)
                ·
                  by_cases h8 : i.val < 144
                  · exact range_sound 8 level8 level9 128 16 (by decide) witnesses8b008 checked8b008
                      ⟨i.val-128,by omega⟩ v i (by change 128+(i.val-128)=i.val; omega)
                  ·
                    by_cases h9 : i.val < 160
                    · exact range_sound 8 level8 level9 144 16 (by decide) witnesses8b009 checked8b009
                        ⟨i.val-144,by omega⟩ v i (by change 144+(i.val-144)=i.val; omega)
                    ·
                      by_cases h10 : i.val < 176
                      · exact range_sound 8 level8 level9 160 16 (by decide) witnesses8b010 checked8b010
                          ⟨i.val-160,by omega⟩ v i (by change 160+(i.val-160)=i.val; omega)
                      ·
                        by_cases h11 : i.val < 192
                        · exact range_sound 8 level8 level9 176 16 (by decide) witnesses8b011 checked8b011
                            ⟨i.val-176,by omega⟩ v i (by change 176+(i.val-176)=i.val; omega)
                        ·
                          by_cases h12 : i.val < 208
                          · exact range_sound 8 level8 level9 192 16 (by decide) witnesses8b012 checked8b012
                              ⟨i.val-192,by omega⟩ v i (by change 192+(i.val-192)=i.val; omega)
                          ·
                            by_cases h13 : i.val < 224
                            · exact range_sound 8 level8 level9 208 16 (by decide) witnesses8b013 checked8b013
                                ⟨i.val-208,by omega⟩ v i (by change 208+(i.val-208)=i.val; omega)
                            ·
                              by_cases h14 : i.val < 240
                              · exact range_sound 8 level8 level9 224 16 (by decide) witnesses8b014 checked8b014
                                  ⟨i.val-224,by omega⟩ v i (by change 224+(i.val-224)=i.val; omega)
                              ·
                                by_cases h15 : i.val < 256
                                · exact range_sound 8 level8 level9 240 16 (by decide) witnesses8b015 checked8b015
                                    ⟨i.val-240,by omega⟩ v i (by change 240+(i.val-240)=i.val; omega)
                                ·
                                  by_cases h16 : i.val < 272
                                  · exact range_sound 8 level8 level9 256 16 (by decide) witnesses8b016 checked8b016
                                      ⟨i.val-256,by omega⟩ v i (by change 256+(i.val-256)=i.val; omega)
                                  ·
                                    exact range_sound 8 level8 level9 272 14 (by decide) witnesses8b017 checked8b017
                                        ⟨i.val-272,by omega⟩ v i (by change 272+(i.val-272)=i.val; omega)
#print axioms step8
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
