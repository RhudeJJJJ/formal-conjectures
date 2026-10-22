/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1172 : Family 10 := level10.get ⟨1458,by decide⟩
def sourceMap1172 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1172 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1172_checked : acceptsGraphIso
    (source (graph core1172) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2295.graph sourceMap1172=true := by decide +kernel
theorem fusedMap1172_checked : acceptsGraphIso
    (fused (graph core1172) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1955.graph fusedMap1172=true := by decide +kernel
theorem certified1172 : Certified (graph core1172) (root 10) 2 2 :=
  of_native_maps core1172 DegreeOneMiddleResidualSpectrum2295.graph DegreeOneMiddleResidualSpectrum1955.graph
    sourceMap1172 fusedMap1172 sourceMap1172_checked fusedMap1172_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1172
#print axioms sourceMap1172_checked
#print axioms fusedMap1172_checked
#print axioms certified1172
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
