/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1180 : Family 10 := level10.get ⟨1542,by decide⟩
def sourceMap1180 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1180 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1180_checked : acceptsGraphIso
    (source (graph core1180) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2336.graph sourceMap1180=true := by decide +kernel
theorem fusedMap1180_checked : acceptsGraphIso
    (fused (graph core1180) (root 10) 2 2) DegreeTwoThreeSpectrum5993.graph fusedMap1180=true := by decide +kernel
theorem certified1180 : Certified (graph core1180) (root 10) 2 2 :=
  of_native_maps core1180 DegreeOneMiddleResidualSpectrum2336.graph DegreeTwoThreeSpectrum5993.graph
    sourceMap1180 fusedMap1180 sourceMap1180_checked fusedMap1180_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1180
#print axioms sourceMap1180_checked
#print axioms fusedMap1180_checked
#print axioms certified1180
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
