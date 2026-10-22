/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1170 : Family 10 := level10.get ⟨1437,by decide⟩
def sourceMap1170 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1170 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1170_checked : acceptsGraphIso
    (source (graph core1170) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2283.graph sourceMap1170=true := by decide +kernel
theorem fusedMap1170_checked : acceptsGraphIso
    (fused (graph core1170) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1953.graph fusedMap1170=true := by decide +kernel
theorem certified1170 : Certified (graph core1170) (root 10) 2 2 :=
  of_native_maps core1170 DegreeOneMiddleResidualSpectrum2283.graph DegreeOneMiddleResidualSpectrum1953.graph
    sourceMap1170 fusedMap1170 sourceMap1170_checked fusedMap1170_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1170
#print axioms sourceMap1170_checked
#print axioms fusedMap1170_checked
#print axioms certified1170
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
