/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4975 : Family 10 := level10.get ⟨1559,by decide⟩
def sourceMap4975 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4975 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4975_checked : acceptsGraphIso
    (source (graph core4975) (root 10) 2 2) DegreeTwoThreeSpectrum7576.graph sourceMap4975=true := by decide +kernel
theorem fusedMap4975_checked : acceptsGraphIso
    (fused (graph core4975) (root 10) 2 2) DegreeTwoThreeSpectrum6022.graph fusedMap4975=true := by decide +kernel
theorem certified4975 : Certified (graph core4975) (root 10) 2 2 :=
  of_native_maps core4975 DegreeTwoThreeSpectrum7576.graph DegreeTwoThreeSpectrum6022.graph
    sourceMap4975 fusedMap4975 sourceMap4975_checked fusedMap4975_checked
    DegreeTwoThreeFiniteComparisons.comparison4975
#print axioms sourceMap4975_checked
#print axioms fusedMap4975_checked
#print axioms certified4975
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
