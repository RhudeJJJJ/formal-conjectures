/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1008 : Family 10 := level10.get ⟨904,by decide⟩
def sourceMap1008 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1008 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1008_checked : acceptsGraphIso
    (source (graph core1008) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2311.graph sourceMap1008=true := by decide +kernel
theorem fusedMap1008_checked : acceptsGraphIso
    (fused (graph core1008) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1449.graph fusedMap1008=true := by decide +kernel
theorem certified1008 : Certified (graph core1008) (root 10) 2 2 :=
  of_native_maps core1008 DegreeOneMiddleResidualSpectrum2311.graph DegreeOneMiddleResidualSpectrum1449.graph
    sourceMap1008 fusedMap1008 sourceMap1008_checked fusedMap1008_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1008
#print axioms sourceMap1008_checked
#print axioms fusedMap1008_checked
#print axioms certified1008
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
