/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1122 : Family 10 := level10.get ⟨1257,by decide⟩
def sourceMap1122 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1122 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1122_checked : acceptsGraphIso
    (source (graph core1122) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2157.graph sourceMap1122=true := by decide +kernel
theorem fusedMap1122_checked : acceptsGraphIso
    (fused (graph core1122) (root 10) 2 2) DegreeTwoThreeSpectrum6505.graph fusedMap1122=true := by decide +kernel
theorem certified1122 : Certified (graph core1122) (root 10) 2 2 :=
  of_native_maps core1122 DegreeOneMiddleResidualSpectrum2157.graph DegreeTwoThreeSpectrum6505.graph
    sourceMap1122 fusedMap1122 sourceMap1122_checked fusedMap1122_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1122
#print axioms sourceMap1122_checked
#print axioms fusedMap1122_checked
#print axioms certified1122
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
