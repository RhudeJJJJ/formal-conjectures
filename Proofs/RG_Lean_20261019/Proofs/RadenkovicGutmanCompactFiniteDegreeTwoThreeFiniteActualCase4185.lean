/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4185 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap4185 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4185 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4185_checked : acceptsGraphIso
    (source (graph core4185) (root 8) 2 2) DegreeTwoThreeSpectrum3844.graph sourceMap4185=true := by decide +kernel
theorem fusedMap4185_checked : acceptsGraphIso
    (fused (graph core4185) (root 8) 2 2) DegreeTwoThreeSpectrum2703.graph fusedMap4185=true := by decide +kernel
theorem certified4185 : Certified (graph core4185) (root 8) 2 2 :=
  of_native_maps core4185 DegreeTwoThreeSpectrum3844.graph DegreeTwoThreeSpectrum2703.graph
    sourceMap4185 fusedMap4185 sourceMap4185_checked fusedMap4185_checked
    DegreeTwoThreeFiniteComparisons.comparison4185
#print axioms sourceMap4185_checked
#print axioms fusedMap4185_checked
#print axioms certified4185
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
