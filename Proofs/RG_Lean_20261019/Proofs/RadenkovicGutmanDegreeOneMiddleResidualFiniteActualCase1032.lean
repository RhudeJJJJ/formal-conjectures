/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1032 : Family 10 := level10.get ⟨1003,by decide⟩
def sourceMap1032 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1032 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1032_checked : acceptsGraphIso
    (source (graph core1032) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1965.graph sourceMap1032=true := by decide +kernel
theorem fusedMap1032_checked : acceptsGraphIso
    (fused (graph core1032) (root 10) 2 2) DegreeTwoThreeSpectrum5985.graph fusedMap1032=true := by decide +kernel
theorem certified1032 : Certified (graph core1032) (root 10) 2 2 :=
  of_native_maps core1032 DegreeOneMiddleResidualSpectrum1965.graph DegreeTwoThreeSpectrum5985.graph
    sourceMap1032 fusedMap1032 sourceMap1032_checked fusedMap1032_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1032
#print axioms sourceMap1032_checked
#print axioms fusedMap1032_checked
#print axioms certified1032
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
