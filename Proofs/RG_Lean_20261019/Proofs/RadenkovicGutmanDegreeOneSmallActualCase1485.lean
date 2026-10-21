/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1485 : Family 9 := level9.get ⟨218,by decide⟩
def sourceMap1485 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1485 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1485_checked : acceptsGraphIso
    (source (graph core1485) (root 9) 0 0) DegreeOneSmallSpectrum760.graph sourceMap1485=true := by decide +kernel
theorem fusedMap1485_checked : acceptsGraphIso
    (fused (graph core1485) (root 9) 0 0) DegreeOneSmallSpectrum525.graph fusedMap1485=true := by decide +kernel
theorem certified1485 : Certified (graph core1485) (root 9) 0 0 :=
  of_native_maps core1485 DegreeOneSmallSpectrum760.graph DegreeOneSmallSpectrum525.graph
    sourceMap1485 fusedMap1485 sourceMap1485_checked fusedMap1485_checked
    DegreeOneSmallComparisons.comparison1485
#print axioms sourceMap1485_checked
#print axioms fusedMap1485_checked
#print axioms certified1485
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
