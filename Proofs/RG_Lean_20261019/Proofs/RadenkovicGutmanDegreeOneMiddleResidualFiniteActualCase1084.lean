/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1084 : Family 10 := level10.get ⟨1126,by decide⟩
def sourceMap1084 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1084 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1084_checked : acceptsGraphIso
    (source (graph core1084) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2064.graph sourceMap1084=true := by decide +kernel
theorem fusedMap1084_checked : acceptsGraphIso
    (fused (graph core1084) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1621.graph fusedMap1084=true := by decide +kernel
theorem certified1084 : Certified (graph core1084) (root 10) 2 2 :=
  of_native_maps core1084 DegreeOneMiddleResidualSpectrum2064.graph DegreeOneMiddleResidualSpectrum1621.graph
    sourceMap1084 fusedMap1084 sourceMap1084_checked fusedMap1084_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1084
#print axioms sourceMap1084_checked
#print axioms fusedMap1084_checked
#print axioms certified1084
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
