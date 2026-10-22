/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1059 : Family 10 := level10.get ⟨1055,by decide⟩
def sourceMap1059 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1059 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1059_checked : acceptsGraphIso
    (source (graph core1059) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2010.graph sourceMap1059=true := by decide +kernel
theorem fusedMap1059_checked : acceptsGraphIso
    (fused (graph core1059) (root 10) 2 2) DegreeTwoThreeSpectrum6097.graph fusedMap1059=true := by decide +kernel
theorem certified1059 : Certified (graph core1059) (root 10) 2 2 :=
  of_native_maps core1059 DegreeOneMiddleResidualSpectrum2010.graph DegreeTwoThreeSpectrum6097.graph
    sourceMap1059 fusedMap1059 sourceMap1059_checked fusedMap1059_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1059
#print axioms sourceMap1059_checked
#print axioms fusedMap1059_checked
#print axioms certified1059
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
