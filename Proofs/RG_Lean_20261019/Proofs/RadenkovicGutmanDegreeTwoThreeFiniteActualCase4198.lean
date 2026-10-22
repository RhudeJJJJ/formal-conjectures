/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4198 : Family 9 := level9.get ⟨37,by decide⟩
def sourceMap4198 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4198 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4198_checked : acceptsGraphIso
    (source (graph core4198) (root 9) 2 2) DegreeTwoThreeSpectrum4557.graph sourceMap4198=true := by decide +kernel
theorem fusedMap4198_checked : acceptsGraphIso
    (fused (graph core4198) (root 9) 2 2) DegreeTwoThreeSpectrum3886.graph fusedMap4198=true := by decide +kernel
theorem certified4198 : Certified (graph core4198) (root 9) 2 2 :=
  of_native_maps core4198 DegreeTwoThreeSpectrum4557.graph DegreeTwoThreeSpectrum3886.graph
    sourceMap4198 fusedMap4198 sourceMap4198_checked fusedMap4198_checked
    DegreeTwoThreeFiniteComparisons.comparison4198
#print axioms sourceMap4198_checked
#print axioms fusedMap4198_checked
#print axioms certified4198
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
