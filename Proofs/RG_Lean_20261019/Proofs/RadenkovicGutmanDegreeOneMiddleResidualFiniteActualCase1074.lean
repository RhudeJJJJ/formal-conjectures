/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1074 : Family 10 := level10.get ⟨1103,by decide⟩
def sourceMap1074 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1074 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1074_checked : acceptsGraphIso
    (source (graph core1074) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2045.graph sourceMap1074=true := by decide +kernel
theorem fusedMap1074_checked : acceptsGraphIso
    (fused (graph core1074) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1604.graph fusedMap1074=true := by decide +kernel
theorem certified1074 : Certified (graph core1074) (root 10) 2 2 :=
  of_native_maps core1074 DegreeOneMiddleResidualSpectrum2045.graph DegreeOneMiddleResidualSpectrum1604.graph
    sourceMap1074 fusedMap1074 sourceMap1074_checked fusedMap1074_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1074
#print axioms sourceMap1074_checked
#print axioms fusedMap1074_checked
#print axioms certified1074
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
