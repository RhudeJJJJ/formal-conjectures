/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1078 : Family 10 := level10.get ⟨1109,by decide⟩
def sourceMap1078 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1078 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1078_checked : acceptsGraphIso
    (source (graph core1078) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2051.graph sourceMap1078=true := by decide +kernel
theorem fusedMap1078_checked : acceptsGraphIso
    (fused (graph core1078) (root 10) 2 2) DegreeTwoThreeSpectrum6205.graph fusedMap1078=true := by decide +kernel
theorem certified1078 : Certified (graph core1078) (root 10) 2 2 :=
  of_native_maps core1078 DegreeOneMiddleResidualSpectrum2051.graph DegreeTwoThreeSpectrum6205.graph
    sourceMap1078 fusedMap1078 sourceMap1078_checked fusedMap1078_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1078
#print axioms sourceMap1078_checked
#print axioms fusedMap1078_checked
#print axioms certified1078
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
