/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1153 : Family 10 := level10.get ⟨1355,by decide⟩
def sourceMap1153 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1153 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1153_checked : acceptsGraphIso
    (source (graph core1153) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2229.graph sourceMap1153=true := by decide +kernel
theorem fusedMap1153_checked : acceptsGraphIso
    (fused (graph core1153) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1789.graph fusedMap1153=true := by decide +kernel
theorem certified1153 : Certified (graph core1153) (root 10) 2 2 :=
  of_native_maps core1153 DegreeOneMiddleResidualSpectrum2229.graph DegreeOneMiddleResidualSpectrum1789.graph
    sourceMap1153 fusedMap1153 sourceMap1153_checked fusedMap1153_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1153
#print axioms sourceMap1153_checked
#print axioms fusedMap1153_checked
#print axioms certified1153
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
