/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1146 : Family 10 := level10.get ⟨1324,by decide⟩
def sourceMap1146 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1146 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1146_checked : acceptsGraphIso
    (source (graph core1146) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2208.graph sourceMap1146=true := by decide +kernel
theorem fusedMap1146_checked : acceptsGraphIso
    (fused (graph core1146) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1768.graph fusedMap1146=true := by decide +kernel
theorem certified1146 : Certified (graph core1146) (root 10) 2 2 :=
  of_native_maps core1146 DegreeOneMiddleResidualSpectrum2208.graph DegreeOneMiddleResidualSpectrum1768.graph
    sourceMap1146 fusedMap1146 sourceMap1146_checked fusedMap1146_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1146
#print axioms sourceMap1146_checked
#print axioms fusedMap1146_checked
#print axioms certified1146
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
