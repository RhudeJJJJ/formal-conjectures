/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1200 : Family 10 := level10.get ⟨1709,by decide⟩
def sourceMap1200 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1200 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1200_checked : acceptsGraphIso
    (source (graph core1200) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2356.graph sourceMap1200=true := by decide +kernel
theorem fusedMap1200_checked : acceptsGraphIso
    (fused (graph core1200) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1715.graph fusedMap1200=true := by decide +kernel
theorem certified1200 : Certified (graph core1200) (root 10) 2 2 :=
  of_native_maps core1200 DegreeOneMiddleResidualSpectrum2356.graph DegreeOneMiddleResidualSpectrum1715.graph
    sourceMap1200 fusedMap1200 sourceMap1200_checked fusedMap1200_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1200
#print axioms sourceMap1200_checked
#print axioms fusedMap1200_checked
#print axioms certified1200
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
