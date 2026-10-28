/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4906 : Family 10 := level10.get ⟨1380,by decide⟩
def sourceMap4906 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4906 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4906_checked : acceptsGraphIso
    (source (graph core4906) (root 10) 2 2) DegreeTwoThreeSpectrum7426.graph sourceMap4906=true := by decide +kernel
theorem fusedMap4906_checked : acceptsGraphIso
    (fused (graph core4906) (root 10) 2 2) DegreeTwoThreeSpectrum6732.graph fusedMap4906=true := by decide +kernel
theorem certified4906 : Certified (graph core4906) (root 10) 2 2 :=
  of_native_maps core4906 DegreeTwoThreeSpectrum7426.graph DegreeTwoThreeSpectrum6732.graph
    sourceMap4906 fusedMap4906 sourceMap4906_checked fusedMap4906_checked
    DegreeTwoThreeFiniteComparisons.comparison4906
#print axioms sourceMap4906_checked
#print axioms fusedMap4906_checked
#print axioms certified4906
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
