/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1066 : Family 10 := level10.get ⟨1072,by decide⟩
def sourceMap1066 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1066 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1066_checked : acceptsGraphIso
    (source (graph core1066) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2024.graph sourceMap1066=true := by decide +kernel
theorem fusedMap1066_checked : acceptsGraphIso
    (fused (graph core1066) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1577.graph fusedMap1066=true := by decide +kernel
theorem certified1066 : Certified (graph core1066) (root 10) 2 2 :=
  of_native_maps core1066 DegreeOneMiddleResidualSpectrum2024.graph DegreeOneMiddleResidualSpectrum1577.graph
    sourceMap1066 fusedMap1066 sourceMap1066_checked fusedMap1066_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1066
#print axioms sourceMap1066_checked
#print axioms fusedMap1066_checked
#print axioms certified1066
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
