/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4613 : Family 10 := level10.get ⟨639,by decide⟩
def sourceMap4613 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4613 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4613_checked : acceptsGraphIso
    (source (graph core4613) (root 10) 2 2) DegreeTwoThreeSpectrum7296.graph sourceMap4613=true := by decide +kernel
theorem fusedMap4613_checked : acceptsGraphIso
    (fused (graph core4613) (root 10) 2 2) DegreeTwoThreeSpectrum5334.graph fusedMap4613=true := by decide +kernel
theorem certified4613 : Certified (graph core4613) (root 10) 2 2 :=
  of_native_maps core4613 DegreeTwoThreeSpectrum7296.graph DegreeTwoThreeSpectrum5334.graph
    sourceMap4613 fusedMap4613 sourceMap4613_checked fusedMap4613_checked
    DegreeTwoThreeFiniteComparisons.comparison4613
#print axioms sourceMap4613_checked
#print axioms fusedMap4613_checked
#print axioms certified4613
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
