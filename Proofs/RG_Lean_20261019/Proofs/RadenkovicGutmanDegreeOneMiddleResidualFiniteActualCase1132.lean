/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1132 : Family 10 := level10.get ⟨1280,by decide⟩
def sourceMap1132 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1132 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1132_checked : acceptsGraphIso
    (source (graph core1132) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2176.graph sourceMap1132=true := by decide +kernel
theorem fusedMap1132_checked : acceptsGraphIso
    (fused (graph core1132) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1736.graph fusedMap1132=true := by decide +kernel
theorem certified1132 : Certified (graph core1132) (root 10) 2 2 :=
  of_native_maps core1132 DegreeOneMiddleResidualSpectrum2176.graph DegreeOneMiddleResidualSpectrum1736.graph
    sourceMap1132 fusedMap1132 sourceMap1132_checked fusedMap1132_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1132
#print axioms sourceMap1132_checked
#print axioms fusedMap1132_checked
#print axioms certified1132
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
