/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4727 : Family 10 := level10.get ⟨949,by decide⟩
def sourceMap4727 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4727 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4727_checked : acceptsGraphIso
    (source (graph core4727) (root 10) 2 2) DegreeTwoThreeSpectrum7550.graph sourceMap4727=true := by decide +kernel
theorem fusedMap4727_checked : acceptsGraphIso
    (fused (graph core4727) (root 10) 2 2) DegreeTwoThreeSpectrum5850.graph fusedMap4727=true := by decide +kernel
theorem certified4727 : Certified (graph core4727) (root 10) 2 2 :=
  of_native_maps core4727 DegreeTwoThreeSpectrum7550.graph DegreeTwoThreeSpectrum5850.graph
    sourceMap4727 fusedMap4727 sourceMap4727_checked fusedMap4727_checked
    DegreeTwoThreeFiniteComparisons.comparison4727
#print axioms sourceMap4727_checked
#print axioms fusedMap4727_checked
#print axioms certified4727
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
