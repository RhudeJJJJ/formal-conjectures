/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0979 : Family 10 := level10.get ⟨844,by decide⟩
def sourceMap0979 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0979 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0979_checked : acceptsGraphIso
    (source (graph core0979) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2278.graph sourceMap0979=true := by decide +kernel
theorem fusedMap0979_checked : acceptsGraphIso
    (fused (graph core0979) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1398.graph fusedMap0979=true := by decide +kernel
theorem certified0979 : Certified (graph core0979) (root 10) 2 2 :=
  of_native_maps core0979 DegreeOneMiddleResidualSpectrum2278.graph DegreeOneMiddleResidualSpectrum1398.graph
    sourceMap0979 fusedMap0979 sourceMap0979_checked fusedMap0979_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0979
#print axioms sourceMap0979_checked
#print axioms fusedMap0979_checked
#print axioms certified0979
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
