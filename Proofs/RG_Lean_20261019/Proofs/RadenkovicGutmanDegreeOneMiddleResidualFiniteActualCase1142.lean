/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1142 : Family 10 := level10.get ⟨1318,by decide⟩
def sourceMap1142 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1142 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1142_checked : acceptsGraphIso
    (source (graph core1142) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2202.graph sourceMap1142=true := by decide +kernel
theorem fusedMap1142_checked : acceptsGraphIso
    (fused (graph core1142) (root 10) 2 2) DegreeTwoThreeSpectrum6624.graph fusedMap1142=true := by decide +kernel
theorem certified1142 : Certified (graph core1142) (root 10) 2 2 :=
  of_native_maps core1142 DegreeOneMiddleResidualSpectrum2202.graph DegreeTwoThreeSpectrum6624.graph
    sourceMap1142 fusedMap1142 sourceMap1142_checked fusedMap1142_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1142
#print axioms sourceMap1142_checked
#print axioms fusedMap1142_checked
#print axioms certified1142
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
