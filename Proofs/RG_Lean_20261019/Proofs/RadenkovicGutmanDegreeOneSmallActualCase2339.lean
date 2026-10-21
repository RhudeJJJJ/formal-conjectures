/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2339 : Family 10 := level10.get ⟨1049,by decide⟩
def sourceMap2339 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2339 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2339_checked : acceptsGraphIso
    (source (graph core2339) (root 10) 0 0) DegreeOneSmallSpectrum1648.graph sourceMap2339=true := by decide +kernel
theorem fusedMap2339_checked : acceptsGraphIso
    (fused (graph core2339) (root 10) 0 0) DegreeOneSmallSpectrum1654.graph fusedMap2339=true := by decide +kernel
theorem certified2339 : Certified (graph core2339) (root 10) 0 0 :=
  of_native_maps core2339 DegreeOneSmallSpectrum1648.graph DegreeOneSmallSpectrum1654.graph
    sourceMap2339 fusedMap2339 sourceMap2339_checked fusedMap2339_checked
    DegreeOneSmallComparisons.comparison2339
#print axioms sourceMap2339_checked
#print axioms fusedMap2339_checked
#print axioms certified2339
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
