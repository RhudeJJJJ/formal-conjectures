/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1025 : Family 10 := level10.get ⟨958,by decide⟩
def sourceMap1025 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1025 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1025_checked : acceptsGraphIso
    (source (graph core1025) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2328.graph sourceMap1025=true := by decide +kernel
theorem fusedMap1025_checked : acceptsGraphIso
    (fused (graph core1025) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1489.graph fusedMap1025=true := by decide +kernel
theorem certified1025 : Certified (graph core1025) (root 10) 2 2 :=
  of_native_maps core1025 DegreeOneMiddleResidualSpectrum2328.graph DegreeOneMiddleResidualSpectrum1489.graph
    sourceMap1025 fusedMap1025 sourceMap1025_checked fusedMap1025_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1025
#print axioms sourceMap1025_checked
#print axioms fusedMap1025_checked
#print axioms certified1025
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
