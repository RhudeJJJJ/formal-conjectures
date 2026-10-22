/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1067 : Family 10 := level10.get ⟨1073,by decide⟩
def sourceMap1067 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1067 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1067_checked : acceptsGraphIso
    (source (graph core1067) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2025.graph sourceMap1067=true := by decide +kernel
theorem fusedMap1067_checked : acceptsGraphIso
    (fused (graph core1067) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1578.graph fusedMap1067=true := by decide +kernel
theorem certified1067 : Certified (graph core1067) (root 10) 2 2 :=
  of_native_maps core1067 DegreeOneMiddleResidualSpectrum2025.graph DegreeOneMiddleResidualSpectrum1578.graph
    sourceMap1067 fusedMap1067 sourceMap1067_checked fusedMap1067_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1067
#print axioms sourceMap1067_checked
#print axioms fusedMap1067_checked
#print axioms certified1067
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
