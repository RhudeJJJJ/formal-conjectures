/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1173 : Family 10 := level10.get ⟨1523,by decide⟩
def sourceMap1173 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1173 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1173_checked : acceptsGraphIso
    (source (graph core1173) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2329.graph sourceMap1173=true := by decide +kernel
theorem fusedMap1173_checked : acceptsGraphIso
    (fused (graph core1173) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1507.graph fusedMap1173=true := by decide +kernel
theorem certified1173 : Certified (graph core1173) (root 10) 2 2 :=
  of_native_maps core1173 DegreeOneMiddleResidualSpectrum2329.graph DegreeOneMiddleResidualSpectrum1507.graph
    sourceMap1173 fusedMap1173 sourceMap1173_checked fusedMap1173_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1173
#print axioms sourceMap1173_checked
#print axioms fusedMap1173_checked
#print axioms certified1173
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
