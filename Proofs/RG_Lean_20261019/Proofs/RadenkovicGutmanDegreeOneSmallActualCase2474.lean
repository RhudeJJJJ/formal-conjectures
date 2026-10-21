/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2474 : Family 10 := level10.get ⟨1614,by decide⟩
def sourceMap2474 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2474 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2474_checked : acceptsGraphIso
    (source (graph core2474) (root 10) 0 0) DegreeOneSmallSpectrum2009.graph sourceMap2474=true := by decide +kernel
theorem fusedMap2474_checked : acceptsGraphIso
    (fused (graph core2474) (root 10) 0 0) DegreeOneSmallSpectrum1697.graph fusedMap2474=true := by decide +kernel
theorem certified2474 : Certified (graph core2474) (root 10) 0 0 :=
  of_native_maps core2474 DegreeOneSmallSpectrum2009.graph DegreeOneSmallSpectrum1697.graph
    sourceMap2474 fusedMap2474 sourceMap2474_checked fusedMap2474_checked
    DegreeOneSmallComparisons.comparison2474
#print axioms sourceMap2474_checked
#print axioms fusedMap2474_checked
#print axioms certified2474
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
