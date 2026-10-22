/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4903 : Family 10 := level10.get ⟨1375,by decide⟩
def sourceMap4903 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4903 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4903_checked : acceptsGraphIso
    (source (graph core4903) (root 10) 2 2) DegreeTwoThreeSpectrum7453.graph sourceMap4903=true := by decide +kernel
theorem fusedMap4903_checked : acceptsGraphIso
    (fused (graph core4903) (root 10) 2 2) DegreeTwoThreeSpectrum6722.graph fusedMap4903=true := by decide +kernel
theorem certified4903 : Certified (graph core4903) (root 10) 2 2 :=
  of_native_maps core4903 DegreeTwoThreeSpectrum7453.graph DegreeTwoThreeSpectrum6722.graph
    sourceMap4903 fusedMap4903 sourceMap4903_checked fusedMap4903_checked
    DegreeTwoThreeFiniteComparisons.comparison4903
#print axioms sourceMap4903_checked
#print axioms fusedMap4903_checked
#print axioms certified4903
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
