/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1182 : Family 10 := level10.get ⟨1545,by decide⟩
def sourceMap1182 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1182 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1182_checked : acceptsGraphIso
    (source (graph core1182) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2338.graph sourceMap1182=true := by decide +kernel
theorem fusedMap1182_checked : acceptsGraphIso
    (fused (graph core1182) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1526.graph fusedMap1182=true := by decide +kernel
theorem certified1182 : Certified (graph core1182) (root 10) 2 2 :=
  of_native_maps core1182 DegreeOneMiddleResidualSpectrum2338.graph DegreeOneMiddleResidualSpectrum1526.graph
    sourceMap1182 fusedMap1182 sourceMap1182_checked fusedMap1182_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1182
#print axioms sourceMap1182_checked
#print axioms fusedMap1182_checked
#print axioms certified1182
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
