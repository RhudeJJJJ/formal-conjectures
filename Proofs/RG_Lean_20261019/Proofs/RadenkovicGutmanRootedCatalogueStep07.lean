/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block000
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block001
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block002
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block003
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block004
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block005
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block006
import Proofs.RadenkovicGutmanRootedCatalogueStep07Block007
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
theorem step7 : ∀ i : Fin level7.length, ∀ v : Vertices 7,
    ∃ j : Fin level8.length,
      ∃ e : graph (n := 8) (level7.get i,v) ≃g graph (level8.get j),
        e (root 8)=root 8 := by
  intro i v
  have hi := i.isLt
  change i.val < 115 at hi
  by_cases h0 : i.val < 16
  · exact range_sound 7 level7 level8 0 16 (by decide) witnesses7b000 checked7b000
      ⟨i.val-0,by omega⟩ v i (by omega)
  ·
    by_cases h1 : i.val < 32
    · exact range_sound 7 level7 level8 16 16 (by decide) witnesses7b001 checked7b001
        ⟨i.val-16,by omega⟩ v i (by omega)
    ·
      by_cases h2 : i.val < 48
      · exact range_sound 7 level7 level8 32 16 (by decide) witnesses7b002 checked7b002
          ⟨i.val-32,by omega⟩ v i (by omega)
      ·
        by_cases h3 : i.val < 64
        · exact range_sound 7 level7 level8 48 16 (by decide) witnesses7b003 checked7b003
            ⟨i.val-48,by omega⟩ v i (by omega)
        ·
          by_cases h4 : i.val < 80
          · exact range_sound 7 level7 level8 64 16 (by decide) witnesses7b004 checked7b004
              ⟨i.val-64,by omega⟩ v i (by omega)
          ·
            by_cases h5 : i.val < 96
            · exact range_sound 7 level7 level8 80 16 (by decide) witnesses7b005 checked7b005
                ⟨i.val-80,by omega⟩ v i (by omega)
            ·
              by_cases h6 : i.val < 112
              · exact range_sound 7 level7 level8 96 16 (by decide) witnesses7b006 checked7b006
                  ⟨i.val-96,by omega⟩ v i (by omega)
              ·
                exact range_sound 7 level7 level8 112 3 (by decide) witnesses7b007 checked7b007
                    ⟨i.val-112,by omega⟩ v i (by omega)
#print axioms step7
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
