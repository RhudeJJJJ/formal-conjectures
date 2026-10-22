/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1007 : Family 10 := level10.get ⟨903,by decide⟩
def sourceMap1007 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1007 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1007_checked : acceptsGraphIso
    (source (graph core1007) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2310.graph sourceMap1007=true := by decide +kernel
theorem fusedMap1007_checked : acceptsGraphIso
    (fused (graph core1007) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1448.graph fusedMap1007=true := by decide +kernel
theorem certified1007 : Certified (graph core1007) (root 10) 2 2 :=
  of_native_maps core1007 DegreeOneMiddleResidualSpectrum2310.graph DegreeOneMiddleResidualSpectrum1448.graph
    sourceMap1007 fusedMap1007 sourceMap1007_checked fusedMap1007_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1007
#print axioms sourceMap1007_checked
#print axioms fusedMap1007_checked
#print axioms certified1007
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
