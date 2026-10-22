/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1021 : Family 10 := level10.get ⟨943,by decide⟩
def sourceMap1021 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1021 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1021_checked : acceptsGraphIso
    (source (graph core1021) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2324.graph sourceMap1021=true := by decide +kernel
theorem fusedMap1021_checked : acceptsGraphIso
    (fused (graph core1021) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1478.graph fusedMap1021=true := by decide +kernel
theorem certified1021 : Certified (graph core1021) (root 10) 2 2 :=
  of_native_maps core1021 DegreeOneMiddleResidualSpectrum2324.graph DegreeOneMiddleResidualSpectrum1478.graph
    sourceMap1021 fusedMap1021 sourceMap1021_checked fusedMap1021_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1021
#print axioms sourceMap1021_checked
#print axioms fusedMap1021_checked
#print axioms certified1021
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
