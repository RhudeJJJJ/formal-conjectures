/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1024 : Family 10 := level10.get ⟨950,by decide⟩
def sourceMap1024 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1024 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1024_checked : acceptsGraphIso
    (source (graph core1024) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2327.graph sourceMap1024=true := by decide +kernel
theorem fusedMap1024_checked : acceptsGraphIso
    (fused (graph core1024) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1484.graph fusedMap1024=true := by decide +kernel
theorem certified1024 : Certified (graph core1024) (root 10) 2 2 :=
  of_native_maps core1024 DegreeOneMiddleResidualSpectrum2327.graph DegreeOneMiddleResidualSpectrum1484.graph
    sourceMap1024 fusedMap1024 sourceMap1024_checked fusedMap1024_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1024
#print axioms sourceMap1024_checked
#print axioms fusedMap1024_checked
#print axioms certified1024
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
