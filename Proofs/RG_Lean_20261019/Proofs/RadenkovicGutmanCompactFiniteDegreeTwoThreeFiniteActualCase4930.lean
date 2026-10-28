/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4930 : Family 10 := level10.get ⟨1442,by decide⟩
def sourceMap4930 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4930 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4930_checked : acceptsGraphIso
    (source (graph core4930) (root 10) 2 2) DegreeTwoThreeSpectrum7530.graph sourceMap4930=true := by decide +kernel
theorem fusedMap4930_checked : acceptsGraphIso
    (fused (graph core4930) (root 10) 2 2) DegreeTwoThreeSpectrum6903.graph fusedMap4930=true := by decide +kernel
theorem certified4930 : Certified (graph core4930) (root 10) 2 2 :=
  of_native_maps core4930 DegreeTwoThreeSpectrum7530.graph DegreeTwoThreeSpectrum6903.graph
    sourceMap4930 fusedMap4930 sourceMap4930_checked fusedMap4930_checked
    DegreeTwoThreeFiniteComparisons.comparison4930
#print axioms sourceMap4930_checked
#print axioms fusedMap4930_checked
#print axioms certified4930
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
