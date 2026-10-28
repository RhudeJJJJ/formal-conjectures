/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4915 : Family 10 := level10.get ⟨1408,by decide⟩
def sourceMap4915 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4915 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4915_checked : acceptsGraphIso
    (source (graph core4915) (root 10) 2 2) DegreeTwoThreeSpectrum7500.graph sourceMap4915=true := by decide +kernel
theorem fusedMap4915_checked : acceptsGraphIso
    (fused (graph core4915) (root 10) 2 2) DegreeTwoThreeSpectrum6808.graph fusedMap4915=true := by decide +kernel
theorem certified4915 : Certified (graph core4915) (root 10) 2 2 :=
  of_native_maps core4915 DegreeTwoThreeSpectrum7500.graph DegreeTwoThreeSpectrum6808.graph
    sourceMap4915 fusedMap4915 sourceMap4915_checked fusedMap4915_checked
    DegreeTwoThreeFiniteComparisons.comparison4915
#print axioms sourceMap4915_checked
#print axioms fusedMap4915_checked
#print axioms certified4915
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
