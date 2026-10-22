/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1022 : Family 10 := level10.get ⟨944,by decide⟩
def sourceMap1022 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1022 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1022_checked : acceptsGraphIso
    (source (graph core1022) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2325.graph sourceMap1022=true := by decide +kernel
theorem fusedMap1022_checked : acceptsGraphIso
    (fused (graph core1022) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1479.graph fusedMap1022=true := by decide +kernel
theorem certified1022 : Certified (graph core1022) (root 10) 2 2 :=
  of_native_maps core1022 DegreeOneMiddleResidualSpectrum2325.graph DegreeOneMiddleResidualSpectrum1479.graph
    sourceMap1022 fusedMap1022 sourceMap1022_checked fusedMap1022_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1022
#print axioms sourceMap1022_checked
#print axioms fusedMap1022_checked
#print axioms certified1022
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
