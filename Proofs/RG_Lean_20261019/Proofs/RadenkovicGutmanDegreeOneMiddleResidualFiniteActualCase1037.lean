/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1037 : Family 10 := level10.get ⟨1012,by decide⟩
def sourceMap1037 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1037 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1037_checked : acceptsGraphIso
    (source (graph core1037) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1973.graph sourceMap1037=true := by decide +kernel
theorem fusedMap1037_checked : acceptsGraphIso
    (fused (graph core1037) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1531.graph fusedMap1037=true := by decide +kernel
theorem certified1037 : Certified (graph core1037) (root 10) 2 2 :=
  of_native_maps core1037 DegreeOneMiddleResidualSpectrum1973.graph DegreeOneMiddleResidualSpectrum1531.graph
    sourceMap1037 fusedMap1037 sourceMap1037_checked fusedMap1037_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1037
#print axioms sourceMap1037_checked
#print axioms fusedMap1037_checked
#print axioms certified1037
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
