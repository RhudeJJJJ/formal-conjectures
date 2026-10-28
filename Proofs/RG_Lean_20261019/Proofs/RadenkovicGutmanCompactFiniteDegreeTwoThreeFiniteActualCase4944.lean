/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4944 : Family 10 := level10.get ⟨1468,by decide⟩
def sourceMap4944 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4944 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4944_checked : acceptsGraphIso
    (source (graph core4944) (root 10) 2 2) DegreeTwoThreeSpectrum7429.graph sourceMap4944=true := by decide +kernel
theorem fusedMap4944_checked : acceptsGraphIso
    (fused (graph core4944) (root 10) 2 2) DegreeTwoThreeSpectrum6949.graph fusedMap4944=true := by decide +kernel
theorem certified4944 : Certified (graph core4944) (root 10) 2 2 :=
  of_native_maps core4944 DegreeTwoThreeSpectrum7429.graph DegreeTwoThreeSpectrum6949.graph
    sourceMap4944 fusedMap4944 sourceMap4944_checked fusedMap4944_checked
    DegreeTwoThreeFiniteComparisons.comparison4944
#print axioms sourceMap4944_checked
#print axioms fusedMap4944_checked
#print axioms certified4944
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
