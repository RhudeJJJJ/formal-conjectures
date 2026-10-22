/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1100 : Family 10 := level10.get ⟨1175,by decide⟩
def sourceMap1100 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1100 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1100_checked : acceptsGraphIso
    (source (graph core1100) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2100.graph sourceMap1100=true := by decide +kernel
theorem fusedMap1100_checked : acceptsGraphIso
    (fused (graph core1100) (root 10) 2 2) DegreeTwoThreeSpectrum6335.graph fusedMap1100=true := by decide +kernel
theorem certified1100 : Certified (graph core1100) (root 10) 2 2 :=
  of_native_maps core1100 DegreeOneMiddleResidualSpectrum2100.graph DegreeTwoThreeSpectrum6335.graph
    sourceMap1100 fusedMap1100 sourceMap1100_checked fusedMap1100_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1100
#print axioms sourceMap1100_checked
#print axioms fusedMap1100_checked
#print axioms certified1100
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
