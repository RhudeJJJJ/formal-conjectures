/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4912 : Family 10 := level10.get ⟨1393,by decide⟩
def sourceMap4912 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4912 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4912_checked : acceptsGraphIso
    (source (graph core4912) (root 10) 2 2) DegreeTwoThreeSpectrum7353.graph sourceMap4912=true := by decide +kernel
theorem fusedMap4912_checked : acceptsGraphIso
    (fused (graph core4912) (root 10) 2 2) DegreeTwoThreeSpectrum6758.graph fusedMap4912=true := by decide +kernel
theorem certified4912 : Certified (graph core4912) (root 10) 2 2 :=
  of_native_maps core4912 DegreeTwoThreeSpectrum7353.graph DegreeTwoThreeSpectrum6758.graph
    sourceMap4912 fusedMap4912 sourceMap4912_checked fusedMap4912_checked
    DegreeTwoThreeFiniteComparisons.comparison4912
#print axioms sourceMap4912_checked
#print axioms fusedMap4912_checked
#print axioms certified4912
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
