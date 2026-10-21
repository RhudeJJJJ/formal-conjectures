/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2248 : Family 10 := level10.get ⟨805,by decide⟩
def sourceMap2248 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2248 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2248_checked : acceptsGraphIso
    (source (graph core2248) (root 10) 0 0) DegreeOneSmallSpectrum1615.graph sourceMap2248=true := by decide +kernel
theorem fusedMap2248_checked : acceptsGraphIso
    (fused (graph core2248) (root 10) 0 0) DegreeOneSmallSpectrum1440.graph fusedMap2248=true := by decide +kernel
theorem certified2248 : Certified (graph core2248) (root 10) 0 0 :=
  of_native_maps core2248 DegreeOneSmallSpectrum1615.graph DegreeOneSmallSpectrum1440.graph
    sourceMap2248 fusedMap2248 sourceMap2248_checked fusedMap2248_checked
    DegreeOneSmallComparisons.comparison2248
#print axioms sourceMap2248_checked
#print axioms fusedMap2248_checked
#print axioms certified2248
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
