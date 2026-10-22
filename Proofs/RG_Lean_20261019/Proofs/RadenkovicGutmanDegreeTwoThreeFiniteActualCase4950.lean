/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4950 : Family 10 := level10.get ⟨1481,by decide⟩
def sourceMap4950 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4950 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4950_checked : acceptsGraphIso
    (source (graph core4950) (root 10) 2 2) DegreeTwoThreeSpectrum7400.graph sourceMap4950=true := by decide +kernel
theorem fusedMap4950_checked : acceptsGraphIso
    (fused (graph core4950) (root 10) 2 2) DegreeTwoThreeSpectrum6971.graph fusedMap4950=true := by decide +kernel
theorem certified4950 : Certified (graph core4950) (root 10) 2 2 :=
  of_native_maps core4950 DegreeTwoThreeSpectrum7400.graph DegreeTwoThreeSpectrum6971.graph
    sourceMap4950 fusedMap4950 sourceMap4950_checked fusedMap4950_checked
    DegreeTwoThreeFiniteComparisons.comparison4950
#print axioms sourceMap4950_checked
#print axioms fusedMap4950_checked
#print axioms certified4950
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
