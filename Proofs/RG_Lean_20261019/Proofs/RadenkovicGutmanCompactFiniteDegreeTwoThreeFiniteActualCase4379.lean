/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4379 : Family 9 := level9.get ⟨548,by decide⟩
def sourceMap4379 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4379 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4379_checked : acceptsGraphIso
    (source (graph core4379) (root 9) 2 2) DegreeTwoThreeSpectrum4906.graph sourceMap4379=true := by decide +kernel
theorem fusedMap4379_checked : acceptsGraphIso
    (fused (graph core4379) (root 9) 2 2) DegreeTwoThreeSpectrum4177.graph fusedMap4379=true := by decide +kernel
theorem certified4379 : Certified (graph core4379) (root 9) 2 2 :=
  of_native_maps core4379 DegreeTwoThreeSpectrum4906.graph DegreeTwoThreeSpectrum4177.graph
    sourceMap4379 fusedMap4379 sourceMap4379_checked fusedMap4379_checked
    DegreeTwoThreeFiniteComparisons.comparison4379
#print axioms sourceMap4379_checked
#print axioms fusedMap4379_checked
#print axioms certified4379
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
