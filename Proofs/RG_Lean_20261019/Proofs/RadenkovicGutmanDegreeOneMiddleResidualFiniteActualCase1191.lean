/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1191 : Family 10 := level10.get ⟨1614,by decide⟩
def sourceMap1191 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1191 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1191_checked : acceptsGraphIso
    (source (graph core1191) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2347.graph sourceMap1191=true := by decide +kernel
theorem fusedMap1191_checked : acceptsGraphIso
    (fused (graph core1191) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1593.graph fusedMap1191=true := by decide +kernel
theorem certified1191 : Certified (graph core1191) (root 10) 2 2 :=
  of_native_maps core1191 DegreeOneMiddleResidualSpectrum2347.graph DegreeOneMiddleResidualSpectrum1593.graph
    sourceMap1191 fusedMap1191 sourceMap1191_checked fusedMap1191_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1191
#print axioms sourceMap1191_checked
#print axioms fusedMap1191_checked
#print axioms certified1191
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
