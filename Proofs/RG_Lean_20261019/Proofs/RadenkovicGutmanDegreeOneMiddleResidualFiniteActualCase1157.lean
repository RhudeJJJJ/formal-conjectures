/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1157 : Family 10 := level10.get ⟨1370,by decide⟩
def sourceMap1157 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1157 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1157_checked : acceptsGraphIso
    (source (graph core1157) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2240.graph sourceMap1157=true := by decide +kernel
theorem fusedMap1157_checked : acceptsGraphIso
    (fused (graph core1157) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1798.graph fusedMap1157=true := by decide +kernel
theorem certified1157 : Certified (graph core1157) (root 10) 2 2 :=
  of_native_maps core1157 DegreeOneMiddleResidualSpectrum2240.graph DegreeOneMiddleResidualSpectrum1798.graph
    sourceMap1157 fusedMap1157 sourceMap1157_checked fusedMap1157_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1157
#print axioms sourceMap1157_checked
#print axioms fusedMap1157_checked
#print axioms certified1157
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
