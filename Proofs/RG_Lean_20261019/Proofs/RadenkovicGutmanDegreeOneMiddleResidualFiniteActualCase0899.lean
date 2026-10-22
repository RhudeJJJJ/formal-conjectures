/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0899 : Family 10 := level10.get ⟨683,by decide⟩
def sourceMap0899 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0899 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0899_checked : acceptsGraphIso
    (source (graph core0899) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2145.graph sourceMap0899=true := by decide +kernel
theorem fusedMap0899_checked : acceptsGraphIso
    (fused (graph core0899) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1232.graph fusedMap0899=true := by decide +kernel
theorem certified0899 : Certified (graph core0899) (root 10) 2 2 :=
  of_native_maps core0899 DegreeOneMiddleResidualSpectrum2145.graph DegreeOneMiddleResidualSpectrum1232.graph
    sourceMap0899 fusedMap0899 sourceMap0899_checked fusedMap0899_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0899
#print axioms sourceMap0899_checked
#print axioms fusedMap0899_checked
#print axioms certified0899
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
