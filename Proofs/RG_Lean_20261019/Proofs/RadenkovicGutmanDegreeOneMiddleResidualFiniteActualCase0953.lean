/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0953 : Family 10 := level10.get ⟨780,by decide⟩
def sourceMap0953 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0953 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0953_checked : acceptsGraphIso
    (source (graph core0953) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2241.graph sourceMap0953=true := by decide +kernel
theorem fusedMap0953_checked : acceptsGraphIso
    (fused (graph core0953) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1320.graph fusedMap0953=true := by decide +kernel
theorem certified0953 : Certified (graph core0953) (root 10) 2 2 :=
  of_native_maps core0953 DegreeOneMiddleResidualSpectrum2241.graph DegreeOneMiddleResidualSpectrum1320.graph
    sourceMap0953 fusedMap0953 sourceMap0953_checked fusedMap0953_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0953
#print axioms sourceMap0953_checked
#print axioms fusedMap0953_checked
#print axioms certified0953
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
