/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0989 : Family 10 := level10.get ⟨863,by decide⟩
def sourceMap0989 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0989 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0989_checked : acceptsGraphIso
    (source (graph core0989) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2291.graph sourceMap0989=true := by decide +kernel
theorem fusedMap0989_checked : acceptsGraphIso
    (fused (graph core0989) (root 10) 2 2) DegreeTwoThreeSpectrum5703.graph fusedMap0989=true := by decide +kernel
theorem certified0989 : Certified (graph core0989) (root 10) 2 2 :=
  of_native_maps core0989 DegreeOneMiddleResidualSpectrum2291.graph DegreeTwoThreeSpectrum5703.graph
    sourceMap0989 fusedMap0989 sourceMap0989_checked fusedMap0989_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0989
#print axioms sourceMap0989_checked
#print axioms fusedMap0989_checked
#print axioms certified0989
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
