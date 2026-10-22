/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4730 : Family 10 := level10.get ⟨954,by decide⟩
def sourceMap4730 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4730 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4730_checked : acceptsGraphIso
    (source (graph core4730) (root 10) 2 2) DegreeTwoThreeSpectrum7482.graph sourceMap4730=true := by decide +kernel
theorem fusedMap4730_checked : acceptsGraphIso
    (fused (graph core4730) (root 10) 2 2) DegreeTwoThreeSpectrum5857.graph fusedMap4730=true := by decide +kernel
theorem certified4730 : Certified (graph core4730) (root 10) 2 2 :=
  of_native_maps core4730 DegreeTwoThreeSpectrum7482.graph DegreeTwoThreeSpectrum5857.graph
    sourceMap4730 fusedMap4730 sourceMap4730_checked fusedMap4730_checked
    DegreeTwoThreeFiniteComparisons.comparison4730
#print axioms sourceMap4730_checked
#print axioms fusedMap4730_checked
#print axioms certified4730
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
