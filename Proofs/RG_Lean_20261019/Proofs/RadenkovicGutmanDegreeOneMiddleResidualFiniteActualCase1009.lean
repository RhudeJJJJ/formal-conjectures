/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1009 : Family 10 := level10.get ⟨908,by decide⟩
def sourceMap1009 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1009 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1009_checked : acceptsGraphIso
    (source (graph core1009) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2312.graph sourceMap1009=true := by decide +kernel
theorem fusedMap1009_checked : acceptsGraphIso
    (fused (graph core1009) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1452.graph fusedMap1009=true := by decide +kernel
theorem certified1009 : Certified (graph core1009) (root 10) 2 2 :=
  of_native_maps core1009 DegreeOneMiddleResidualSpectrum2312.graph DegreeOneMiddleResidualSpectrum1452.graph
    sourceMap1009 fusedMap1009 sourceMap1009_checked fusedMap1009_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1009
#print axioms sourceMap1009_checked
#print axioms fusedMap1009_checked
#print axioms certified1009
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
